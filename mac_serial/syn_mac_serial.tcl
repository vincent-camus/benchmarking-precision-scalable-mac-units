##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  synthesis script for mac_serial
## Version:   2.0
## Notes:     for external DVFS framework
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############
	
    # Design
    set DESIGN       mac_serial
    set RTL_FILE     ../auto/mac_serial/mac_serial.sv
    
    # Entity
    set ENTITY       mac_serial_2_2

    # Delays
    set CLK_2B       0.300
    set CLK_4B       0.400
    set CLK_8B       0.600

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-$CLK_2B-sdc2
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_serial/batch
    set SDC_PATH     ../auto/mac_serial/constraints
    set REPORT_PATH  ./test_serial
    set EXPORT_PATH  ./test_serial
    
    # Lib
    set LIB_DB       /scratch/camus/common/dkits/tcbn28hplbwptt1v25c_ccs.lib 
    
    # Reporting
    puts "\033\[41;97;1mManual processing of $FULLNAME\033\[0m"

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
ungroup /designs/top_mac_serial/mac/* -flatten
set_attribute ungroup_ok true *
set_attribute ungroup_ok false mac

############### INFORMATION ###############

# Get parameters from entity name
regexp -linestop {_(\d+)_(\d+)$} $ENTITY MATCHED N_WIDTH W_CONFIG_WIDTH

# Effective throughput (ignoring activations, only weights matter)
echo "\n############### EFFECTIVE THROUGHPUT\n"             >  $REPORT_PATH/$FULLNAME.rpt
for {set W_CHOSEN_WIDTH 2}                   {$W_CHOSEN_WIDTH <= 8} {set W_CHOSEN_WIDTH [expr {2*$W_CHOSEN_WIDTH}]} {
    for {set A_CHOSEN_WIDTH $W_CHOSEN_WIDTH} {$A_CHOSEN_WIDTH <= 8} {set A_CHOSEN_WIDTH [expr {2*$A_CHOSEN_WIDTH}]} {
        set W_REQUIRED_WIDTH [expr {max(8/(2**$W_CONFIG_WIDTH), $N_WIDTH, $W_CHOSEN_WIDTH)}]
        set CYCLE_PER_CALC   [expr {$W_REQUIRED_WIDTH/$N_WIDTH                            }]
        set THROUGHPUT       [expr {1.0/$CYCLE_PER_CALC                                   }]
        echo "Mode ${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b: $THROUGHPUT" >> $REPORT_PATH/$FULLNAME.rpt
    }
}

# SDC version
echo "\n############### SDC - CHECK\n"                      >> $REPORT_PATH/$FULLNAME.rpt
echo "SDC script: $SDC_PATH/${DESIGN}_$W_CONFIG_WIDTH.sdc"  >> $REPORT_PATH/$FULLNAME.rpt 

############### CONSTRAINTS ###############

# Apply SDC
redirect -variable RPT_SDC {read_sdc $SDC_PATH/${DESIGN}_$W_CONFIG_WIDTH.sdc}
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
echo "\n############### TIMING - FROM MULT ACCU\n"          >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from mac/mult_accu_reg[*]           >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO MULT ACCU\n"            >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/mult_accu_reg[*]           >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO Z\n"                    >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/z_reg[*]                   >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM Z TO Z\n"             >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from mac/z_reg[*] -to mac/z_reg[*]  >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM FSM LAST\n"           >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from fsm_last_reg_reg               >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM FSM ACCU\n"           >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from fsm_accu_reg_reg               >> $REPORT_PATH/$FULLNAME.rpt

# Area reports
echo "\n############### AREA - SUMMARY\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report area                                                 >> $REPORT_PATH/$FULLNAME.rpt

# Power reports
echo "\n############### POWER - SUMMARY\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report power                                                >> $REPORT_PATH/$FULLNAME.rpt

# Clean-up
#delete_obj designs/*
