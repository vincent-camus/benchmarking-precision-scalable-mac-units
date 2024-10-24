##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  power bench simulation script for mac_serial2d
## Version:   1.1
## Notes:     SDC 2 (5-mode), stimuli/lib parameters, new dump name
##-----------------------------------------------------

if {[info exists AUTO]} {

    # Auto-mode defines its own parameters
    puts "\033\[41;97;1mAutomatic processing\033\[0m"

} else {

    ############ DESIGN PARAMETERS ############

    set DESIGN          mac_serial2d_4

    # Files
    set VERILOG_FILE    ../syn/test_serial2d/${DESIGN}_clk:1.1-0.9-0.7-sdc2.v
    set SDF_FILE        ../syn/test_serial2d/${DESIGN}_clk:1.1-0.9-0.7-sdc2.sdf
    set PB_FILE         ../auto/mac_serial2d/pb/pb_${DESIGN}.sv
    
    # Directories
    #set ASSERT_DIR      ### no assertion file for this design ! ###
    
    # Simulation mode
    set CLK_PERIOD      0.6
    set A_CHOSEN_WIDTH  8
    set W_CHOSEN_WIDTH  2

    # Setup
    set STIMULI_MAX     1000
    set LIB_V           /scratch/camus/common/dkits/tcbn28hplbwp.v
    
    # Reporting
    puts "\033\[41;97;1mManual processing of $VERILOG_FILE\033\[0m"

}

# Get AW_CONFIG_WIDTH from verilog file name
regexp -linestop {mac_serial2d_(\d+)_} $VERILOG_FILE MATCHED N_WIDTH

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -quiet -work work $LIB_V
vlog        -work work $VERILOG_FILE
vlog -sv    -work work $PB_FILE

############## SIMULATION & WAVEFORM #############

if {[info exists AUTO]} {
   
    # Run sim
    vsim pb_mac_serial2d -t 100fs \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
        -G N_WIDTH=$N_WIDTH \
        -sdfmax top_mac_serial2d=$SDF_FILE

} else {

    # Run sim
    vsim pb_mac_serial2d -t 100fs \
        -G CLK_PERIOD=${CLK_PERIOD}ns \
        -G W_CHOSEN_WIDTH=$W_CHOSEN_WIDTH \
        -G A_CHOSEN_WIDTH=$A_CHOSEN_WIDTH \
        -G STIMULI_FILE=/scratch/camus/common/rand/rand_w${W_CHOSEN_WIDTH}_a${A_CHOSEN_WIDTH}.csv \
        -G STIMULI_MAX=$STIMULI_MAX \
        -G VCD_FILE=dump_${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b_clk${CLK_PERIOD}.vcd \
		-G N_WIDTH=$N_WIDTH \
        -novopt \
        -sdfmax top_mac_serial2d=$SDF_FILE
        # -sdfnowarn -sdfnoerror -noglitch -suppress 3584

        # Waveform
        add wave -height 10 -divider  "bench"
        add wave -radix unsigned      sim:/W_CHOSEN_WIDTH
		add wave -radix unsigned      sim:/W_ACTIVE_WIDTH
        add wave -radix unsigned      sim:/A_CHOSEN_WIDTH
		add wave -radix unsigned      sim:/A_ACTIVE_WIDTH

        add wave -height 10 -divider  "config"
        add wave -radix binary        sim:/clk_fast
		add wave -radix binary        sim:/clk_slow
        add wave -radix binary        sim:/mode
        add wave -radix binary        sim:/rst
        add wave -radix binary        sim:/rst_mult
        add wave -radix binary        sim:/rst_mult_delayed
        add wave -radix binary        sim:/rst_mult_delayed2
        add wave -radix binary        sim:/pb_mac_serial2d/top_mac_serial2d/rst_mult
        add wave -radix binary        sim:/shift_ctr
        add wave -radix binary        sim:/sign_ctr 

        add wave -height 40 -divider  "inputs/outputs"
        add wave -radix unsigned      sim:/a_sel
        add wave -radix signed        sim:/w_sel
        add wave -radix unsigned      sim:/a
        add wave -radix signed        sim:/w
        add wave -radix unsigned      sim:/a_o
        add wave -radix signed        sim:/w_o
        add wave -radix signed        sim:/z
        add wave -radix signed        sim:/rst_delayed
        add wave -radix signed        sim:/z_exp
        add wave -radix signed        sim:/z_exp_delayed
        add wave -radix signed        sim:/z_exp_delayed2
        add wave -radix signed        sim:/z_exp_delayed3
        #add wave                      sim:/assert__accumulation

        add wave -height 40 -divider  "top_mac" 
        add wave -radix binary -r     sim:/pb_mac_serial2d/top_mac_serial2d/*

        add wave -height 40 -divider  "mac" 
        add wave -radix binary -r     sim:/pb_mac_serial2d/top_mac_serial2d/mac/*

}

#################### RUN ALL #####################

run -all

################### AUTO QUIT ####################

if {[info exists AUTO]} {
    quit -sim
    exit
}
