##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  power bench simulation script for mac_bfusion
## Version:   2.0
## Notes:     SDC 2 (5-mode), stimuli/lib parameters, new dump name
##-----------------------------------------------------

if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Files
    set VERILOG_FILE    ../syn/test_bfusion/mac_bfusion_1_clk:1.1-0.9-0.7-sdc2.v
    set SDF_FILE        ../syn/test_bfusion/mac_bfusion_1_clk:1.1-0.9-0.7-sdc2.sdc
    set PB_FILE         ../auto/mac_bfusion/pb/pb_mac_bfusion_1.sv
    
    # Directories
    #set ASSERT_DIR      ### no assertion file for this design ! ###
    
    # Simulation mode
    set CLK_PERIOD      5.000
    set A_CHOSEN_WIDTH  8
    set W_CHOSEN_WIDTH  2

    # Setup
    set STIMULI_MAX     1000
    set LIB_V           /scratch/camus/common/dkits/tcbn28hplbwp.v
    
    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"

}

# Get AW_CONFIG_WIDTH from verilog file name
regexp -linestop {mac_bfusion_(\d+)_} $VERILOG_FILE MATCHED SCALABLE_LEVELS

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work $LIB_V
vlog        -work work $VERILOG_FILE
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {

    # Run sim
    vsim pb_mac_bfusion -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G SCALABLE_LEVELS=$SCALABLE_LEVELS \
        -sdfmax top_mac_bfusion=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_bfusion -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
		-G SCALABLE_LEVELS=$SCALABLE_LEVELS \
        -novopt
        # -sdfmax top_mac_bfusion=$SDF_FILE \
        # -sdfnowarn -sdfnoerror -noglitch -suppress 3584

        # Waveform
        add wave -height 10 -divider  "bench"
        add wave -radix binary        sim:/mode
        add wave -radix unsigned      sim:/W_CHOSEN_WIDTH
		add wave -radix unsigned      sim:/W_ACTIVE_WIDTH
        add wave -radix unsigned      sim:/A_CHOSEN_WIDTH
		add wave -radix unsigned      sim:/A_ACTIVE_WIDTH

        add wave -height 10 -divider  "config"
        add wave -radix binary        sim:/clk

        add wave -radix binary        sim:/config_aw
        add wave -radix binary        sim:/rst
        add wave -radix binary        sim:/accu_rst

        add wave -height 40 -divider  "inputs/outputs"
        add wave -radix unsigned      sim:/a
        add wave -radix signed        sim:/w
        add wave -radix signed        sim:/z

        add wave -height 40 -divider  "top_mac" 
        add wave -radix binary -r     sim:/pb_mac_bfusion/top_mac_bfusion/*

        add wave -height 40 -divider  "mac" 
        add wave -radix binary -r     sim:/pb_mac_bfusion/top_mac_bfusion/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
