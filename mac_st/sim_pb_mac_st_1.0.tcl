##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: syn_mac_st_1.0.tcl
## Function:  power bench simulation script for mac_st
## Version:   1.0
##-----------------------------------------------------

if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Files
    set VERILOG_FILE    ../syn/test_st/mac_st_1_clk:1.1-0.9-0.7.v
    set SDF_FILE        ../syn/test_st/mac_st_1_clk:1.1-0.9-0.7.sdf
    set PB_FILE         ../auto/mac_st/pb_mac_st_1.0.sv
    
    # Directories
    #set ASSERT_DIR      ../auto/mac_st/assertions_1.0/   ### no assertion file ###
    
    # Simulation mode
    set CLK_PERIOD      1.5
    set W_CHOSEN_WIDTH  2
    set A_CHOSEN_WIDTH  2

    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"

}

# Get AW_CONFIG_WIDTH from verilog file name
regexp -linestop {mac_st_(\d+)_} $VERILOG_FILE MATCHED AW_CONFIG_WIDTH

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work /scratch/camus/common/dkits/tcbn28hplbwp.v
vlog        -work work $VERILOG_FILE
#vlog -sv    -work work $ASSERT_DIR/assertion_binding_$AW_CONFIG_WIDTH.sv   ### no assertion file ###
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {

    # Run sim
    vsim pb_mac_st -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=10000 \
        -G VCD_FILE=dump_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}_clk${CLK_PERIOD}.vcd \
        -G CONFIG_AW_WIDTH=$AW_CONFIG_WIDTH \
        -sdfmax top_mac_st=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_st -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=50000 \
        -G VCD_FILE=dump_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}_clk${CLK_PERIOD}.vcd \
        -G CONFIG_AW_WIDTH=$AW_CONFIG_WIDTH \
        -sdfmax top_mac_st=$SDF_FILE \
        -novopt -sdfnowarn -noglitch -suppress 3584
        # -sdfnowarn -sdfnoerror -noglitch -suppress 3584

        # Waveform
        add wave -height 10 -divider  "config"
        add wave -radix binary        sim:/clk
        add wave -radix binary        sim:/config_aw
        add wave -radix binary        sim:/rst
        add wave -radix binary        sim:/accu_rst

        add wave -height 40 -divider  "inputs/outputs"
        add wave -radix unsigned      sim:/a
        add wave -radix signed        sim:/w
        add wave -radix signed        sim:/z

        #add wave -height 40 -divider  "assertions"    ### no assertion file ###
        #add wave                      sim:/top_mac_st/sva/assert__accumulation_reset
        #add wave                      sim:/top_mac_st/sva/assert__accumulation_mode1
        #add wave                      sim:/top_mac_st/sva/assert__accumulation_mode2
        #add wave                      sim:/top_mac_st/sva/assert__accumulation_mode4

        add wave -height 40 -divider  "top_mac" 
        add wave -radix binary -r     sim:/pb_mac_st/top_mac_st/*

        add wave -height 40 -divider  "mac" 
        add wave -radix binary -r     sim:/pb_mac_st/top_mac_st/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
