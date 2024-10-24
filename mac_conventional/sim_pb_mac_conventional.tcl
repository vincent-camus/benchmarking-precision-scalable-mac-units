##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  power bench simulation script for mac_conventional
## Version:   2.0
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Files
    set VERILOG_FILE    ../syn/test_conventional/mac_conventional_clk:0.8-0.5-0.3-sdc2.v
    set SDF_FILE        ../syn/test_conventional/mac_conventional_clk:0.8-0.5-0.3-sdc2.sdf
    set PB_FILE         ../auto/mac_conventional/pb_mac_conventional.sv
    
    # Simulation mode
    set CLK_PERIOD      0.844
    set W_CHOSEN_WIDTH  8
    set A_CHOSEN_WIDTH  8
    
    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"
    
    # Setup
    set STIMULI_MAX     10000
    set LIB_V           /scratch/camus/common/dkits/tcbn28hplbwp.v
    
}

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work $LIB_V
vlog        -work work $VERILOG_FILE
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {

    # Run sim
    vsim pb_mac_conventional -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -sdfmax top_mac_conventional=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_conventional -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -sdfmax top_mac_conventional=$SDF_FILE \
        -novopt
        # -sdfnowarn -sdfnoerror -noglitch -suppress 3584

        # Waveform
        add wave -height 10 -divider                          "config and general"
        add wave -radix binary                                sim:/clk
        add wave -radix binary                                sim:/rst
        add wave -radix binary                                sim:/accu_rst
        add wave -height 10 -divider                          "assertions" 
        add wave                                              sim:/assert__reset
        add wave                                              sim:/assert__accumulation
        add wave -height 10 -divider                          "accumulation"
        add wave -radix binary                   -color white sim:/w
        add wave -radix binary                   -color white sim:/a
        add wave -radix signed   -format literal              sim:/z
        add wave -height 10 -divider                          "top_mac"
        #add wave -r                                           sim:/pb_mac_conventional/top_mac_conventional/*
        add wave -height 10 -divider                          "mac"
        #add wave -r                                           sim:/pb_mac_conventional/top_mac_conventional/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
