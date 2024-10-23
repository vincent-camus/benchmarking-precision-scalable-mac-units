##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: sim_tb_mac_multiplex_1.0.tcl
## Function:  test bench simulation script for mac_multiplex
## Version:   1.0
##-----------------------------------------------------

################# COMPILE SOURCE #################

vlib work
vmap work work

vlog -sv -work work ../auto/mac_multiplex/mac_multiplex_1.1.sv
vlog -sv -work work ../auto/mac_multiplex/batch_1.0/mac_multiplex_2.sv

vlog -sv -work work ../auto/mac_multiplex/assertions_1.0/assertion_binding_2.sv
vlog -sv -work work ../auto/mac_multiplex/tb_mac_multiplex_1.0.sv

################### SIMULATION ###################

vsim tb_mac_multiplex -t ps -novopt

add wave -height 10 -divider                          "config and general"
add wave -radix unsigned                              sim:/aw_bits
add wave -radix binary                                sim:/config_aw
add wave -radix binary                                sim:/clk
add wave -radix binary                                sim:/rst
add wave -radix binary                                sim:/accu_rst

add wave -height 10 -divider                          "function debug"
add wave -radix signed                                sim:/top_mac/mac/sc_matrix
add wave -radix signed                                sim:/top_mac/mac/sc_index
add wave -radix signed                                sim:/top_mac/mac/gc_index

add wave -height 10 -divider                          "assertions" 
add wave sim:/tb_mac_multiplex/top_mac/sva/assert__accumulation_reset
add wave sim:/tb_mac_multiplex/top_mac/sva/assert__accumulation_mode1
add wave sim:/tb_mac_multiplex/top_mac/sva/assert__accumulation_mode2
add wave sim:/tb_mac_multiplex/top_mac/sva/assert__accumulation_mode4

add wave -height 50 -divider                          "mode 1"
add wave -radix binary                   -color white sim:/w
add wave -radix binary                   -color white sim:/a
add wave -radix binary                                sim:/clk
add wave -height 10 -divider                          "mult"
add wave -radix binary                                sim:/top_mac/mac/mult_tmp
add wave -height 10 -divider                          "mult"
add wave -radix signed   -format literal -color blue  sim:/m_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[3][0]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[3][0]}
add wave -radix signed   -format literal -color blue  sim:/z_exp
add wave -radix signed   -format literal              sim:/z


add wave -height 50 -divider                          "mode 2"
add wave -radix binary                                sim:/clk
add wave -radix binary                                sim:/w
add wave -radix binary                                sim:/a
add wave -radix binary                                sim:/clk
add wave -height 10 -divider                          "mult"
add wave -radix binary                                sim:/top_mac/mac/mult_tmp
add wave -height 10 -divider                          "mult0"
add wave -radix signed   -format literal -color white sim:/w0_mode2
add wave -radix unsigned -format literal -color white sim:/a0_mode2
add wave -radix signed   -format literal -color blue  sim:/m0_mode2_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[2][0]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[2][0]}
add wave -radix signed   -format literal -color blue  sim:/z0_mode2_exp
add wave -radix signed   -format literal              sim:/z0_mode2
add wave -height 10 -divider                          "mult1"
add wave -radix signed   -format literal -color white sim:/w1_mode2
add wave -radix unsigned -format literal -color white sim:/a1_mode2
add wave -radix signed   -format literal -color blue  sim:/m1_mode2_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[2][1]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[2][1]}
add wave -radix signed   -format literal -color blue  sim:/z1_mode2_exp
add wave -radix signed   -format literal              sim:/z1_mode2

add wave -height 50 -divider                          "mode 4"
add wave -radix binary                                sim:/w
add wave -radix binary                                sim:/a
add wave -radix binary                                sim:/clk
add wave -height 10 -divider                          "mult"
add wave -radix binary                                sim:/top_mac/mac/mult_tmp
add wave -height 10 -divider                          "mult0"
add wave -radix signed   -format literal -color white sim:/w0_mode4
add wave -radix unsigned -format literal -color white sim:/a0_mode4
add wave -radix signed   -format literal -color blue  sim:/m0_mode4_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[1][0]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[1][0]}
add wave -radix signed   -format literal -color blue  sim:/z0_mode4_exp
add wave -radix signed   -format literal              sim:/z0_mode4
add wave -height 10 -divider                          "mult1"
add wave -radix signed   -format literal -color white sim:/w1_mode4
add wave -radix unsigned -format literal -color white sim:/a1_mode4
add wave -radix signed   -format literal -color blue  sim:/m1_mode4_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[1][1]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[1][1]}
add wave -radix signed   -format literal -color blue  sim:/z1_mode4_exp
add wave -radix signed   -format literal              sim:/z1_mode4
add wave -height 10 -divider                          "mult2"
add wave -radix signed   -format literal -color white sim:/w2_mode4
add wave -radix unsigned -format literal -color white sim:/a2_mode4
add wave -radix signed   -format literal -color blue  sim:/m2_mode4_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[1][2]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[1][2]}
add wave -radix signed   -format literal -color blue  sim:/z2_mode4_exp
add wave -radix signed   -format literal              sim:/z2_mode4
add wave -height 10 -divider                          "mult3"
add wave -radix signed   -format literal -color white sim:/w3_mode4
add wave -radix unsigned -format literal -color white sim:/a3_mode4
add wave -radix signed   -format literal -color blue  sim:/m3_mode4_exp
add wave -radix binary   -format literal             {sim:/top_mac/mac/ps[1][3]}
add wave -radix signed   -format literal             {sim:/top_mac/mac/ps_integer[1][3]}
add wave -radix signed   -format literal -color blue  sim:/z3_mode4_exp
add wave -radix signed   -format literal              sim:/z3_mode4

add wave -height 50 -divider                          "partial products"
add wave -radix binary                               {sim:/top_mac/mac/ps[0]}

add wave -height 50 -divider                          "others"
add wave -r /*

run -all
