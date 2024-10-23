##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: sim_pb_mac_serial_2.0.tcl
## Function:  power bench simulation script for mac_serial
## Version:   2.0
##-----------------------------------------------------


if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    # Files
    set VERILOG_FILE    ../syn/test_serial/mac_serial_2_2_clk:0.600-0.400-0.300-sdc2.v 
    set SDF_FILE        ../syn/test_serial/mac_serial_2_2_clk:0.600-0.400-0.300-sdc2.sdf
    set PB_FILE         ../auto/mac_serial/pb_mac_serial_1.9.sv
    
    # Simulation mode
    set CLK_PERIOD      0.430
    set W_CHOSEN_WIDTH  4
    set A_CHOSEN_WIDTH  4

    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"
    
    # Setup
    set STIMULI_MAX     10000
    set LIB_V           /scratch/camus/common/dkits/tcbn28hplbwp.v

}

# Get N_WIDTH and CONFIG_W_WIDTH from verilog file name
regexp -linestop {serial_(\d+)_(\d+)_} $VERILOG_FILE MATCHED N_WIDTH W_CONFIG_WIDTH

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work $LIB_V
vlog        -work work $VERILOG_FILE
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {

    # Run sim
     vsim pb_mac_serial -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G N_WIDTH=$N_WIDTH \
        -G CONFIG_W_WIDTH=$W_CONFIG_WIDTH \
        -sdfmax top_mac_serial=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_serial -t ps \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G N_WIDTH=$N_WIDTH \
        -G CONFIG_W_WIDTH=$W_CONFIG_WIDTH \
        -sdfmax top_mac_serial=$SDF_FILE \
        -novopt
        #+neg_tchk
        # -sdfnowarn -sdfnoerror -noglitch -suppress 3584

    # Waveform
    add wave -divider "config"
    add wave -radix binary    sim:/pb_mac_serial/config_w
    add wave -radix binary    sim:/pb_mac_serial/fsm_last
    add wave -radix binary    sim:/pb_mac_serial/fsm_accu
    add wave -radix binary    sim:/pb_mac_serial/rst
    add wave -radix binary    sim:/pb_mac_serial/clk
    add wave -radix binary    sim:/pb_mac_serial/clk_accu
     
    add wave -divider "bench"
    add wave -radix unsigned  sim:/pb_mac_serial/a_line
    add wave -radix signed    sim:/pb_mac_serial/w_line

    add wave -divider "inputs/outputs"
    add wave -radix unsigned  sim:/pb_mac_serial/a
    add wave -radix signed    sim:/pb_mac_serial/w
    add wave -radix binary    sim:/pb_mac_serial/w_serial
    add wave -radix signed    sim:/pb_mac_serial/z

    add wave -divider "assertions" 
    add wave                  sim:/pb_mac_serial/assert__accumulation
    add wave                  sim:/pb_mac_serial/assert__reset
        
    add wave -divider "UUT top_mac_serial" 
    add wave                  sim:/pb_mac_serial/top_mac_serial/*

    add wave -divider "mac" 
    add wave                  sim:/pb_mac_serial/top_mac_serial/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
