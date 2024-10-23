##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: syn_mac_bfusion_2.0.tcl
## Function:  synthesis script for mac_bfusion
## Version:   2.0
## Notes:     With SDC 2.0 (5-mode) and external DVFS
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Design
    set DESIGN       mac_bfusion
    set RTL_FILE     nc
    
    # Entity
    set ENTITY       mac_bfusion_2

    # Delays
    set CLK_2B       0.7
    set CLK_4B       0.9
    set CLK_8B       1.1

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-$CLK_2B-sdc2
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_bfusion/batch_1.0
    set SDC_PATH     ../auto/mac_bfusion/constraints_2.0
    set REPORT_PATH  ./test_bfusion
    set EXPORT_PATH  ./test_bfusion

   
    # Lib
    set LIB_DB       /scratch/camus/common/dkits/tcbn28hplbwptt1v25c_ccs.lib

    # Reporting
    puts "\033\[41;97;1mManual processing of $FULLNAME\033\[0m"

}

################# LIBRARY #################

set_attribute library $LIB_DB

############# ANALYZE SOURCE ##############

# Special case for MAC SS: entity-specific RTL file
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
ungroup /designs/top_mac_bfusion/mac/* -flatten
set_attribute ungroup_ok true *
set_attribute ungroup_ok false mac

############### INFORMATION ###############

# Get parameters from entity name
regexp -linestop {mac_bfusion_(\d+)$} $ENTITY MATCHED SCALABLE_LEVELS

# Effective throughput (special case manual)
echo "\n############### EFFECTIVE THROUGHPUT\n"              >> $REPORT_PATH/$FULLNAME.rpt
if {$SCALABLE_LEVELS == 2} {
    echo "Mode 2b_2b: 16"   >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 4b_2b: -999" >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_2b: 4"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 4b_4b: 4"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_4b: 2"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_8b: 1"    >> $REPORT_PATH/$FULLNAME.rpt
} elseif {$SCALABLE_LEVELS == 1} {
    echo "Mode 2b_2b: 4"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 4b_2b: -999" >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_2b: 2"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 4b_4b: 4"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_4b: 2"    >> $REPORT_PATH/$FULLNAME.rpt
    echo "Mode 8b_8b: 1"    >> $REPORT_PATH/$FULLNAME.rpt
} else {
    echo "Error/Failure writing effective throughtput"  >> $REPORT_PATH/$FULLNAME.rpt
    puts "Error/Failure writing effective throughtput $FULLNAME"
    exit 3
}

# SDC version
echo "\n############### SDC - CHECK\n"                      >> $REPORT_PATH/$FULLNAME.rpt
echo "SDC script: $SDC_PATH/$ENTITY.sdc"                    >> $REPORT_PATH/$FULLNAME.rpt 

############### CONSTRAINTS ###############

# Apply SDC
redirect -variable RPT_SDC {read_sdc $SDC_PATH/$ENTITY.sdc}
echo $RPT_SDC                                              >> $REPORT_PATH/$FULLNAME.rpt

################# COMPILE #################

syn_generic
syn_map

################# EXPORTS #################

write_hdl              > $EXPORT_PATH/$FULLNAME.v
write_sdf -version 3.0 > $EXPORT_PATH/$FULLNAME.sdf

################# REPORTS #################

# Timing reports
echo   "############### TIMING - SUMMARY\n"                  >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary                                       >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM A\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from a_reg_reg[*]                    >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM W\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from w_reg_reg[*]                    >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM ACCU RST\n"            >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from accu_rst_reg_reg                >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO MULT REG\n "             >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/*mult_reg[*]                >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - TO Z\n"                     >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -to   mac/*z_reg[*]                   >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### TIMING - FROM Z TO Z\n"              >> $REPORT_PATH/$FULLNAME.rpt
report timing -summary -from mac/*z_reg[*] -to mac/*z_reg[*] >> $REPORT_PATH/$FULLNAME.rpt

# Area reports
echo "\n############### AREA - SUMMARY\n"                    >> $REPORT_PATH/$FULLNAME.rpt
report area                                                  >> $REPORT_PATH/$FULLNAME.rpt

# Power reports
echo "\n############### POWER - SUMMARY\n"                   >> $REPORT_PATH/$FULLNAME.rpt
report power -verbose                                        >> $REPORT_PATH/$FULLNAME.rpt

# Gate reports
echo "\n############### GATES - TOP SUMMARY\n"               >> $REPORT_PATH/$FULLNAME.rpt
report gates -power                                          >> $REPORT_PATH/$FULLNAME.rpt
echo "\n############### GATES - MAC SUMMARY\n"               >> $REPORT_PATH/$FULLNAME.rpt
report gates -instance_hier mac -power                       >> $REPORT_PATH/$FULLNAME.rpt

# Clean-up
#delete_obj designs/*