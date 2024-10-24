##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  power bench simulation script for mac_multiplex
## Version:   2.0
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Files
    set VERILOG_FILE    ../syn/test_multiplex/mac_multiplex_2_clk:1.30-1.20-0.85_sdc2.0.v
    set SDF_FILE        ../syn/test_multiplex/mac_multiplex_2_clk:1.30-1.20-0.85_sdc2.0.sdf
    set PB_FILE         ../auto/mac_multiplex/pb_mac_multiplex.sv
    
    # Directories
    set ASSERT_DIR      ../auto/mac_multiplex/assertions/
    
    # Simulation mode
    set CLK_PERIOD      1.5
    set W_CHOSEN_WIDTH  4
    set A_CHOSEN_WIDTH  8

    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"
    
    # Setup
    set STIMULI_MAX     5000
    set LIB_V           /scratch/camus/common/dkits/tcbn28hplbwp.v

}

# Get AW_CONFIG_WIDTH from verilog file name
regexp -linestop {multiplex_(\d+)_} $VERILOG_FILE MATCHED AW_CONFIG_WIDTH

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work $LIB_V
vlog        -work work $VERILOG_FILE
vlog -sv    -work work $ASSERT_DIR/assertion_binding_$AW_CONFIG_WIDTH.sv
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {

    # Run sim
    vsim pb_mac_multiplex -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G CONFIG_AW_WIDTH=$AW_CONFIG_WIDTH \
        -sdfmax top_mac_multiplex=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_multiplex -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G CONFIG_AW_WIDTH=$AW_CONFIG_WIDTH \
        -sdfmax top_mac_multiplex=$SDF_FILE \
        -novopt
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
        add wave -radix binary        sim:/top_mac_multiplex/mac/mult

        add wave -height 40 -divider  "assertions" 
        add wave                      sim:/top_mac_multiplex/sva/assert__accumulation_reset
        add wave                      sim:/top_mac_multiplex/sva/assert__accumulation_mode1
        add wave                      sim:/top_mac_multiplex/sva/assert__accumulation_mode2
        add wave                      sim:/top_mac_multiplex/sva/assert__accumulation_mode4

        add wave -height 40 -divider  "top_mac" 
        add wave -radix binary -r     sim:/pb_mac_multiplex/top_mac_multiplex/*

        add wave -height 40 -divider  "mac" 
        add wave -radix binary -r     sim:/pb_mac_multiplex/top_mac_multiplex/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
