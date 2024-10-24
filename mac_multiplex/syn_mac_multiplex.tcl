##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  synthesis script for mac_multiplex
## Version:   2.0
## Notes:     new lib
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Design
    set DESIGN       mac_multiplex
    set RTL_FILE     ../auto/mac_multiplex/mac_multiplex.sv
    
    # Entity
    set ENTITY       mac_multiplex_2

    # Delays
    set CLK_2B       0.85
    set CLK_4B       1.20
    set CLK_8B       1.30

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-${CLK_2B}_sdc2.0-dvfs
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_multiplex/batch
    set SDC_PATH     ../auto/mac_multiplex/constraints
    set REPORT_PATH  ./test_multiplex
    set EXPORT_PATH  ./test_multiplex
    
    # Lib
    set LIB_DB       /scratch/camus/common/dkits/tcbn28hpmbwp35tt0p9v25c_ccs.lib
    set LIB_DB_LOW   /scratch/camus/common/dkits/tcbn28hpmbwp35tt0p8v25c_ccs.lib
    set LIB_DB_HIGH  /scratch/camus/common/dkits/tcbn28hpmbwp35tt1v25c_ccs.lib

    # Reporting
    puts "\033\[41;97;1mProcessing $FULLNAME\033\[0m"

}

################# LIBRARY #################

set_attribute library $LIB_DB

############# ANALYZE SOURCE ##############

read_hdl -library work -sv $RTL_FILE
read_hdl -library work -sv $BATCH_PATH/$ENTITY.sv

############### ELABORATION ###############

# General compilation settings
set_attribute lp_insert_clock_gating true /
set_attribute syn_global_effort high
set_attribute ungroup true

# Elaboration
elaborate top_$DESIGN
check_design
uniquify top_$DESIGN

# Clock gating from 2 flip-flops
set_attribute lp_clock_gating_min_flops 2 /designs/*

# Ungroup all but mac
ungroup /designs/top_mac_multiplex/mac/* -flatten
set_attribute ungroup_ok true *
set_attribute ungroup_ok false mac

############### INFORMATION ###############

# Get parameters from entity name
regexp -linestop {_(\d+)$} $ENTITY MATCHED CONFIG_AW_WIDTH

# Effective throughput
echo "\n############### EFFECTIVE THROUGHPUT\n"              >> $REPORT_PATH/$FULLNAME.rpt
for {set W_CHOSEN_WIDTH 2}                   {$W_CHOSEN_WIDTH <= 8} {set W_CHOSEN_WIDTH [expr {2*$W_CHOSEN_WIDTH}]} {
    for {set A_CHOSEN_WIDTH $W_CHOSEN_WIDTH} {$A_CHOSEN_WIDTH <= 8} {set A_CHOSEN_WIDTH [expr {2*$A_CHOSEN_WIDTH}]} {
        set MAX_CHOSEN_WIDTH   [expr {max($A_CHOSEN_WIDTH, $W_CHOSEN_WIDTH)}]
        set AW_EFFECTIVE_WIDTH [expr {max(8/(2**$CONFIG_AW_WIDTH), $MAX_CHOSEN_WIDTH)}]
        set THROUGHPUT         [expr {8/$AW_EFFECTIVE_WIDTH}]
        echo "Mode ${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b: $THROUGHPUT" >> $REPORT_PATH/$FULLNAME.rpt
    }
}

# SDC version
echo "\n############### SDC - CHECK\n"                       >> $REPORT_PATH/$FULLNAME.rpt
echo "SDC script: $SDC_PATH/${DESIGN}_$CONFIG_AW_WIDTH.sdc"  >> $REPORT_PATH/$FULLNAME.rpt 

############### CONSTRAINTS ###############

# Apply SDC
redirect -variable RPT_SDC {read_sdc $SDC_PATH/${DESIGN}_$CONFIG_AW_WIDTH.sdc}
echo $RPT_SDC                                               >> $REPORT_PATH/$FULLNAME.rpt

################# COMPILE #################

syn_generic
syn_map

################# EXPORTS #################

write_hdl              > $EXPORT_PATH/$FULLNAME.v
write_sdf -version 3.0 > $EXPORT_PATH/$FULLNAME.sdf

################# REPORTS #################

# Timing reports
echo   "############### TIMING - SUMMARY\n"                 >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary                                      >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM A\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from a_reg_reg[*]                   >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM W\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from w_reg_reg[*]                   >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM ACCU RST\n"           >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from accu_rst_reg_reg               >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO MULT REG\n "            >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/mult_reg[*]                >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO Z\n"                    >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/z_reg[*]                   >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM Z TO Z\n"             >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from mac/z_reg[*] -to mac/z_reg[*]  >> $REPORT_PATH/$FULLNAME.rpt

# Area reports
echo "\n############### AREA - SUMMARY\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report area                                                 >> $REPORT_PATH/$FULLNAME.rpt

# Power reports
echo "\n############### POWER - SUMMARY\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report power                                                >> $REPORT_PATH/$FULLNAME.rpt

################## DVFS ###################

# Load double library 0.8-0.9V
set_attribute library "{ $LIB_DB_LOW $LIB_DB }"
echo "\nLibraries: $LIB_DB_LOW"                             >> $REPORT_PATH/$FULLNAME.rpt
echo   "           $LIB_DB\n"                               >> $REPORT_PATH/$FULLNAME.rpt

# Loop on voltage
for {set VOLTAGE 0.800} {$VOLTAGE < 0.900} {set VOLTAGE [format "%.3f" [expr {$VOLTAGE + 0.025}]]} {
    
    # Set voltage condition
    set_attribute voltage $VOLTAGE [get_attribute active_operating_conditions /]
    
    # Timing report
    echo "\n############### TIMING ${VOLTAGE}V - SUMMARY\n" >> $REPORT_PATH/$FULLNAME.rpt
    report timing -summary                                  >> $REPORT_PATH/$FULLNAME.rpt
}

# Load double library 0.9-1.0V
set_attribute library "{ $LIB_DB $LIB_DB_HIGH }"
echo "\nLibraries: $LIB_DB"                                 >> $REPORT_PATH/$FULLNAME.rpt
echo   "           $LIB_DB_HIGH\n"                          >> $REPORT_PATH/$FULLNAME.rpt

# Loop on voltage
for {set VOLTAGE 0.900} {$VOLTAGE <= 1.000} {set VOLTAGE [format "%.3f" [expr {$VOLTAGE + 0.025}]]} {
    
    # Set voltage condition
    set_attribute voltage $VOLTAGE [get_attribute active_operating_conditions /]
    
    # Timing report
    echo "\n############### TIMING ${VOLTAGE}V - SUMMARY\n" >> $REPORT_PATH/$FULLNAME.rpt
    report timing -summary                                  >> $REPORT_PATH/$FULLNAME.rpt
}

# Clean-up
#delete_obj designs/*
