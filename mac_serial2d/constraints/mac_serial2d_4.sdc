##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  SDC constraints for mac_serial2d with N_WIDTH=4
## Version:   2.0.2
##-----------------------------------------------------

############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 0 mode[0]
set_case_analysis 0 mode[1]
set_case_analysis 0 mode[2]
#
set_case_analysis 0 mac/mode[0]
set_case_analysis 0 mac/mode[1]
set_case_analysis 0 mac/mode[2]
#

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk*]

set_case_analysis 1 mode[0]
set_case_analysis 1 mode[1]
set_case_analysis 1 mode[2]
#
set_case_analysis 1 mac/mode[0]
set_case_analysis 1 mac/mode[1]
set_case_analysis 1 mac/mode[2]
#

# fixed input-bit selection

set_case_analysis 0 shift_ctr_reg_reg/q
set_case_analysis 0 a_sel_reg_reg/q
set_case_analysis 0 w_sel_reg_reg/q

# symmetrically data-gated mult registers

set_case_analysis 0 mac/mult_accu_r_reg[0]/q
set_case_analysis 0 mac/mult_accu_r_reg[1]/q
set_case_analysis 0 mac/mult_accu_r_reg[2]/q
set_case_analysis 0 mac/mult_accu_r_reg[3]/q
set_case_analysis 0 mac/mult_accu_r_reg[4]/q
set_case_analysis 0 mac/mult_accu_r_reg[5]/q
set_case_analysis 0 mac/mult_accu_r_reg[6]/q
set_case_analysis 0 mac/mult_accu_r_reg[7]/q
set_case_analysis 0 mac/mult_accu_r_reg[8]/q
set_case_analysis 0 mac/mult_accu_r_reg[9]/q
set_case_analysis 0 mac/mult_accu_r_reg[10]/q
set_case_analysis 0 mac/mult_accu_r_reg[11]/q

# symmetrically data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q
set_case_analysis 0 mac/z_reg[6]/q
set_case_analysis 0 mac/z_reg[7]/q

############### 2-BIT MODE ################

set_constraint_mode 2b_2b
create_clock -name "clk" -period $CLK_2B [get_ports clk*]

set_case_analysis 1 mode[0]
set_case_analysis 1 mode[1]
set_case_analysis 1 mode[2]
#
set_case_analysis 1 mac/mode[0]
set_case_analysis 1 mac/mode[1]
set_case_analysis 1 mac/mode[2]
#

# fixed input-bit selection

set_case_analysis 0 shift_ctr_reg_reg/q
set_case_analysis 0 a_sel_reg_reg/q
set_case_analysis 0 w_sel_reg_reg/q

# symmetrically data-gated a input

set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 mac/a[0]
set_case_analysis 0 mac/a[1]

# symmetrically data-gated w input

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/w[1]

# symmetrically data-gated mult registers

set_case_analysis 0 mac/mult_accu_r_reg[0]/q
set_case_analysis 0 mac/mult_accu_r_reg[1]/q
set_case_analysis 0 mac/mult_accu_r_reg[2]/q
set_case_analysis 0 mac/mult_accu_r_reg[3]/q
set_case_analysis 0 mac/mult_accu_r_reg[4]/q
set_case_analysis 0 mac/mult_accu_r_reg[5]/q
set_case_analysis 0 mac/mult_accu_r_reg[6]/q
set_case_analysis 0 mac/mult_accu_r_reg[7]/q
set_case_analysis 0 mac/mult_accu_r_reg[8]/q
set_case_analysis 0 mac/mult_accu_r_reg[9]/q
set_case_analysis 0 mac/mult_accu_r_reg[10]/q
set_case_analysis 0 mac/mult_accu_r_reg[11]/q

set_case_analysis 0 mac/mult_accu_c_reg[0]/q
set_case_analysis 0 mac/mult_accu_c_reg[1]/q
set_case_analysis 0 mac/mult_accu_c_reg[2]/q
set_case_analysis 0 mac/mult_accu_c_reg[3]/q

# symmetrically data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q
set_case_analysis 0 mac/z_reg[6]/q
set_case_analysis 0 mac/z_reg[7]/q
set_case_analysis 0 mac/z_reg[8]/q
set_case_analysis 0 mac/z_reg[9]/q
set_case_analysis 0 mac/z_reg[10]/q
set_case_analysis 0 mac/z_reg[11]/q

######### WEIGHT-ONLY 4-BIT MODE ##########

set_constraint_mode 8b_4b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 1 mode[0]
set_case_analysis 0 mode[1]
set_case_analysis 0 mode[2]
#
set_case_analysis 1 mac/mode[0]
set_case_analysis 0 mac/mode[1]
set_case_analysis 0 mac/mode[2]
#

# fixed input-bit selection

set_case_analysis 0 w_sel_reg_reg/q

# weight-only data-gated mult registers

set_case_analysis 0 mac/mult_accu_r_reg[0]/q
set_case_analysis 0 mac/mult_accu_r_reg[1]/q
set_case_analysis 0 mac/mult_accu_r_reg[2]/q
set_case_analysis 0 mac/mult_accu_r_reg[3]/q

# weight-only data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q

######### WEIGHT-ONLY 2-BIT MODE ##########

set_constraint_mode 8b_2b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 1 mode[0]
set_case_analysis 0 mode[1]
set_case_analysis 0 mode[2]
#
set_case_analysis 1 mac/mode[0]
set_case_analysis 0 mac/mode[1]
set_case_analysis 0 mac/mode[2]
#

# fixed input-bit selection

set_case_analysis 0 w_sel_reg_reg/q

# data-gated w input

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/w[1]

# weight-only data-gated mult registers

set_case_analysis 0 mac/mult_accu_r_reg[0]/q
set_case_analysis 0 mac/mult_accu_r_reg[1]/q
set_case_analysis 0 mac/mult_accu_r_reg[2]/q
set_case_analysis 0 mac/mult_accu_r_reg[3]/q
set_case_analysis 0 mac/mult_accu_r_reg[4]/q
set_case_analysis 0 mac/mult_accu_r_reg[5]/q
# Correction !!!
# Correction !!!
set_case_analysis 0 mac/mult_accu_r_reg[8]/q
set_case_analysis 0 mac/mult_accu_r_reg[9]/q

# weight-only data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q
