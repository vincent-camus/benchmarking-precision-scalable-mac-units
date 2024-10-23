##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: syn_mac_st_1.0.tcl
## Function:  synthesis script for mac_st
## Version:   1.0
## Notes:     auto clock-gating with from 2 flip-flops
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Design
    set DESIGN       mac_st
    set RTL_FILE     ../auto/mac_st/mac_st_1.0.sv
    
    # Entity
    set ENTITY       mac_st_2

    # Delays
    set CLK_2B       0.7
    set CLK_4B       0.9
    set CLK_8B       1.1

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-$CLK_2B
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_st/batch_1.0
    set SDC_PATH     ../auto/mac_st/constraints_1.0
    set REPORT_PATH  ./test_st
    set EXPORT_PATH  ./test_st

    # Reporting
    puts "\033\[41;97;1mProcessing $FULLNAME\033\[0m"

}

################# LIBRARY #################

set_attribute library /scratch/camus/common/dkits/tcbn28hplbwptt1v25c_ccs.lib

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
ungroup /designs/top_mac_st/mac/* -flatten
set_attribute ungroup_ok true *
set_attribute ungroup_ok false mac

############### INFORMATION ###############

# Get parameters from entity name
regexp -linestop {_(\d+)$} $ENTITY MATCHED CONFIG_AW_WIDTH

# Effective throughput
echo "\n############### EFFECTIVE THROUGHPUT\n"             >> $REPORT_PATH/$FULLNAME.rpt
echo "Delay type:  max (i.e. max delay and min throughput)" >> $REPORT_PATH/$FULLNAME.rpt
for {set AW_CHOSEN_WIDTH 2} {$AW_CHOSEN_WIDTH <= 8} {set AW_CHOSEN_WIDTH [expr {2*$AW_CHOSEN_WIDTH}]} {
    set AW_EFFECTIVE_WIDTH [expr {max(8/(2**$CONFIG_AW_WIDTH), $AW_CHOSEN_WIDTH)}]
	set THROUGHPUT         [expr {8/$AW_EFFECTIVE_WIDTH}]
    echo "Mode $AW_CHOSEN_WIDTH:      $THROUGHPUT"          >> $REPORT_PATH/$FULLNAME.rpt
}

# SDC version
echo "\n############### SDC - CHECK\n"                      >> $REPORT_PATH/$FULLNAME.rpt
echo "SDC script: $SDC_PATH/${DESIGN}_$CONFIG_AW_WIDTH.sdc" >> $REPORT_PATH/$FULLNAME.rpt 

############### CONSTRAINTS ###############

# Apply SDC
redirect -variable RPT_SDC {read_sdc $SDC_PATH/${DESIGN}_$CONFIG_AW_WIDTH.sdc}
echo $RPT_SDC                                              >> $REPORT_PATH/$FULLNAME.rpt

################# COMPILE #################

syn_generic
syn_map

################# EXPORTS #################

write_hdl              > $EXPORT_PATH/$FULLNAME.v
write_sdf -version 3.0 > $EXPORT_PATH/$FULLNAME.sdf

################# REPORTS #################

# Timing reports
echo   "############### TIMING - SUMMARY\n"                >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary                                     >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM A\n"                 >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from a_reg_reg[*]                  >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM W\n"                 >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from w_reg_reg[*]                  >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM ACCU RST\n"          >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from accu_rst_reg_reg              >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO MULT REG\n "           >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/mult_reg[*]               >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO Z\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/z_reg[*]                  >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM Z TO Z\n"            >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from mac/z_reg[*] -to mac/z_reg[*] >> $REPORT_PATH/$FULLNAME.rpt

# Area reports
echo "\n############### AREA - SUMMARY\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report area                                                >> $REPORT_PATH/$FULLNAME.rpt

# Power reports
echo "\n############### POWER - SUMMARY\n"                 >> $REPORT_PATH/$FULLNAME.rpt
report power                                               >> $REPORT_PATH/$FULLNAME.rpt

# Clean-up
#delete_obj designs/*

