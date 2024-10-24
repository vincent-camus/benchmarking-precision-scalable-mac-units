##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  test bench simulation script for mac_conventional
## Version:   1.0
##-----------------------------------------------------

################# COMPILE SOURCE #################

#quit -sim -force
#restart -force
#rm work -rf

vlib work
vmap work work

# clock-gated version
vlog -sv -work work ../auto/mac_conventional/mac_conventional.sv
vlog -sv -work work ../auto/mac_conventional/batch/mac_conventional.sv

vlog -sv -work work ../auto/mac_conventional/tb_mac_conventional.sv


################### SIMULATION ###################

vsim tb_mac_conventional -t ps -novopt

add wave -height 10 -divider                          "config and general"
add wave -radix unsigned                              sim:/w_bits
add wave -radix unsigned                              sim:/a_bits
add wave -radix binary                                sim:/clk
add wave -radix binary                                sim:/rst
add wave -radix binary                                sim:/accu_rst

add wave -height 10 -divider                          "assertions" 
add wave                                              sim:/assert__reset
add wave                                              sim:/assert__accumulation
add wave                                              sim:/assert__overflow

add wave -height 50 -divider                          "accumulation"
add wave -radix binary                   -color white sim:/w
add wave -radix binary                   -color white sim:/a
add wave -radix binary                                sim:/clk
add wave -height 10 -divider                          "mult"
add wave -radix binary                                sim:/top_mac/mac/mult_tmp
add wave -height 10 -divider                          "mult"
add wave -radix signed   -format literal -color blue  sim:/mult_exp
add wave -radix signed   -format literal -color blue  sim:/z_exp
add wave -radix signed   -format literal              sim:/z

add wave -height 50 -divider                          "top_mac"
add wave -r                                           sim:/top_mac/*

add wave -height 50 -divider                          "mac"
add wave -r                                           sim:/top_mac/mac/*

run -all