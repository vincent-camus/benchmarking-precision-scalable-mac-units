##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: syn_mac_conventional_1.0.tcl
## Function:  synthesis script for mac_conventional
## Version:   1.0
## Notes:     auto clock-gating with from 2 flip-flops (same as mac_serial)
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############
	
    # Design
    set DESIGN       mac_conventional
    set RTL_FILE     ../auto/mac_conventional/mac_conventional_1.0.sv
    
    # Entity
    set ENTITY       mac_conventional

    # Delays
    set CLK_2B       0.3
    set CLK_4B       0.5
    set CLK_8B       0.8

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-$CLK_2B
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_conventional/batch_1.0
    set SDC_PATH     ../auto/mac_conventional/constraints_1.0
    set REPORT_PATH  ./test
    set EXPORT_PATH  ./test

    # Reporting
    puts "\033\[41;97;1mManual processing of $FULLNAME\033\[0m"

}

################# LIBRARY #################

set_attribute library /scratch/camus/common/tcbn28hplbwptt1v25c_ccs.lib

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
ungroup /designs/top_mac_conventional/mac/* -flatten
set_attribute ungroup_ok true *
set_attribute ungroup_ok false mac

############### INFORMATION ###############

# Effective throughput
echo "\n############### EFFECTIVE THROUGHPUT\n"             >> $REPORT_PATH/$FULLNAME.rpt
echo "Delay type:  max (i.e. max delay and min throughput)" >> $REPORT_PATH/$FULLNAME.rpt
for {set AW_CHOSEN_WIDTH 2} {$AW_CHOSEN_WIDTH <= 8} {set AW_CHOSEN_WIDTH [expr {2*$AW_CHOSEN_WIDTH}]} {
    echo "Mode $AW_CHOSEN_WIDTH:      1"                    >> $REPORT_PATH/$FULLNAME.rpt
}

# SDC version
echo "\n############### SDC - CHECK\n"                      >> $REPORT_PATH/$FULLNAME.rpt
echo "SDC script: $SDC_PATH/${DESIGN}.sdc"                  >> $REPORT_PATH/$FULLNAME.rpt 

############### CONSTRAINTS ###############

# Apply SDC
redirect -variable RPT_SDC {read_sdc $SDC_PATH/${DESIGN}.sdc}
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
echo "\n############### TIMING - FROM RST\n"               >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from rst_reg_reg                   >> $REPORT_PATH/$FULLNAME.rpt
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
