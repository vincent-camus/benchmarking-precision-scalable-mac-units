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
    set CLK_2B       0.600
    set CLK_4B       0.850
    set CLK_8B       1.100

    # Design name
    set MAPPING      clk:$CLK_8B-$CLK_4B-${CLK_2B}_asym
    set FULLNAME     ${ENTITY}_$MAPPING

    # Paths
    set BATCH_PATH   ../auto/mac_conventional/batch_1.0
    set SDC_PATH     ../auto/mac_conventional/constraints_1.0
    set REPORT_PATH  ./test_conventional_dvfs
    set EXPORT_PATH  ./test_conventional_dvfs

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

set_attribute library {{ /scratch/camus/common/dkits/tcbn28hplbwptt0p8v25c_ccs.lib /scratch/camus/common/dkits/tcbn28hplbwptt1v25c_ccs.lib }}

for {set VOLTAGE 0.80} {$VOLTAGE <= 1.00} {set VOLTAGE [format "%.2f" [expr {$VOLTAGE + 0.05}]]} {

    # set voltage condition
    set_attribute voltage $VOLTAGE [get_attribute active_operating_conditions /]
    
    # write big report
    echo   "############### TIMING $VOLTAGE V\n"           >> $REPORT_PATH/${FULLNAME}.rpt
    report timing -summary                                 >> $REPORT_PATH/${FULLNAME}.rpt
    
    # write small report
    redirect -variable TIMING {report timing -summary}
    regexp {Timing slack +: +([-0-9]+)ps.*Mode +: +2b.*Timing slack +: +([-0-9]+)ps.*Mode +: +4b.*Timing slack +: +([-0-9]+)ps.*Mode +: +8b} \
        $TIMING MATCHED SLACK_2B SLACK_4B SLACK_8B
    set DELAY_2B [format "%.3f" [expr {$CLK_2B - ($SLACK_2B / 1000.0) }]]
    set DELAY_4B [format "%.3f" [expr {$CLK_4B - ($SLACK_4B / 1000.0) }]]
    set DELAY_8B [format "%.3f" [expr {$CLK_8B - ($SLACK_8B / 1000.0) }]]
    echo "$FULLNAME,   $VOLTAGE,    $DELAY_2B,    $DELAY_4B,   $DELAY_8B" >> $REPORT_PATH/all_reports.csv

}
