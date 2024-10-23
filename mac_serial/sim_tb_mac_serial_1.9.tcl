##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: sim_tb_mac_serial_1.9.tcl
## Function:  test bench simulation script for mac_serial
## Version:   1.9
##-----------------------------------------------------

################# COMPILE SOURCE #################

#quit -sim -force
#restart -force
#rm work -rf

vlib work
vmap work work

vlog -sv -work work ../auto/mac_serial/mac_serial_1.9.sv
vlog -sv -work work ../auto/mac_serial/batch_1.9/mac_serial_1_2.sv
vlog -sv -work work ../auto/mac_serial/tb_mac_serial_1.9.sv

################### SIMULATION ###################

vsim tb_mac_serial -t ps -novopt

add wave -divider "config"
add wave -radix unsigned  sim:/tb_mac_serial/w_bits
add wave -radix binary    sim:/tb_mac_serial/config_w
add wave -radix binary    sim:/tb_mac_serial/fsm_last
add wave -radix binary    sim:/tb_mac_serial/fsm_accu
add wave -radix binary    sim:/tb_mac_serial/rst
add wave -radix binary    sim:/tb_mac_serial/clk
add wave -radix binary    sim:/tb_mac_serial/clk_accu

add wave -divider "##### DEBUG #####"
add wave -radix unsigned  -color blue sim:/tb_mac_serial/fsm_accu
add wave -radix binary    -color blue sim:/tb_mac_serial/UUT/fsm_accu
add wave -radix binary    -color blue sim:/tb_mac_serial/UUT/clk_accu

add wave -divider "inputs/outputs"
add wave -radix unsigned  sim:/tb_mac_serial/a
add wave -radix signed    sim:/tb_mac_serial/w
add wave -radix signed    sim:/tb_mac_serial/mult_exp
add wave -radix signed    sim:/tb_mac_serial/z_exp
add wave -radix signed    sim:/tb_mac_serial/z

add wave -divider "assertions" 
add wave                  sim:/tb_mac_serial/assert__accumulation
add wave                  sim:/tb_mac_serial/assert__reset

add wave -divider "bench"
add wave -radix binary    sim:*

add wave -divider "UUT"
add wave                  sim:/tb_mac_serial/UUT/mac/ps
add wave -radix binary -r sim:/tb_mac_serial/UUT/*

run -all
