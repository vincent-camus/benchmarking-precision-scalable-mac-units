##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: mac_serial_1.sdc
## Function:  SDC constraints for mac_serial with CONFIG_W_WIDTH=1
## Notes:     STA considering symmetric inputs with data-gating of input a and w_serial
## Version:   2.0
##-----------------------------------------------------

##     !!!!!!!!!!!!!!!!!!!!!!!!!!!
##     !  For 4-bit serial ONLY  !
##     !!!!!!!!!!!!!!!!!!!!!!!!!!!

############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 0 config_w[0]
set_case_analysis 0 mac/config_w[0]

#
#

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk*]

set_case_analysis 1 config_w[0]
set_case_analysis 1 mac/config_w[0]

#
#

# symmetrically data-gated mult registers

set_case_analysis 0 mac/mult_accu_reg[0]/q
set_case_analysis 0 mac/mult_accu_reg[1]/q
set_case_analysis 0 mac/mult_accu_reg[2]/q
set_case_analysis 0 mac/mult_accu_reg[3]/q
set_case_analysis 0 mac/mult_accu_reg[4]/q
set_case_analysis 0 mac/mult_accu_reg[5]/q
set_case_analysis 0 mac/mult_accu_reg[6]/q
set_case_analysis 0 mac/mult_accu_reg[7]/q

# symmetrically data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q
set_case_analysis 0 mac/z_reg[6]/q
set_case_analysis 0 mac/z_reg[7]/q

# symmetrically data-gated inputs (a input only for 1-bit and 2-bit serial)

set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]
set_case_analysis 0 a_reg_reg[0]/q
set_case_analysis 0 a_reg_reg[1]/q
set_case_analysis 0 a_reg_reg[2]/q
set_case_analysis 0 a_reg_reg[3]/q

############### 2-BIT MODE ################

set_constraint_mode 2b_2b
create_clock -name "clk" -period $CLK_2B [get_ports clk*]

set_case_analysis 1 config_w[0]
set_case_analysis 1 mac/config_w[0]

#
#

# symmetrically data-gated mult registers

set_case_analysis 0 mac/mult_accu_reg[0]/q
set_case_analysis 0 mac/mult_accu_reg[1]/q
set_case_analysis 0 mac/mult_accu_reg[2]/q
set_case_analysis 0 mac/mult_accu_reg[3]/q
set_case_analysis 0 mac/mult_accu_reg[4]/q
set_case_analysis 0 mac/mult_accu_reg[5]/q
set_case_analysis 0 mac/mult_accu_reg[6]/q
set_case_analysis 0 mac/mult_accu_reg[7]/q
set_case_analysis 0 mac/mult_accu_reg[8]/q
set_case_analysis 0 mac/mult_accu_reg[9]/q
set_case_analysis 0 mac/mult_accu_reg[10]/q
set_case_analysis 0 mac/mult_accu_reg[11]/q

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

# symmetrically data-gated a input

set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]
set_case_analysis 0 a[4]
set_case_analysis 0 a[5]
set_case_analysis 0 a_reg_reg[0]/q
set_case_analysis 0 a_reg_reg[1]/q
set_case_analysis 0 a_reg_reg[2]/q
set_case_analysis 0 a_reg_reg[3]/q
set_case_analysis 0 a_reg_reg[4]/q
set_case_analysis 0 a_reg_reg[5]/q

# symmetrically data-gated w_serial input (!!! for 4-bit serial !!!)

set_case_analysis 0 w_serial[0]
set_case_analysis 0 w_serial[1]
set_case_analysis 0 w_serial_reg_reg[0]/q
set_case_analysis 0 w_serial_reg_reg[1]/q

######### WEIGHT-ONLY 4-BIT MODE ##########

set_constraint_mode 8b_4b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 1 config_w[0]
set_case_analysis 1 mac/config_w[0]

#
#

# weight-only data-gated mult register (TO CHECK: NO COMPENSATION???)

set_case_analysis 0 mac/mult_accu_reg[0]/q
set_case_analysis 0 mac/mult_accu_reg[1]/q
set_case_analysis 0 mac/mult_accu_reg[2]/q
set_case_analysis 0 mac/mult_accu_reg[3]/q

# weight-only data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q

######### WEIGHT-ONLY 2-BIT MODE ##########

set_constraint_mode 8b_2b
create_clock -name "clk" -period $CLK_8B [get_ports clk*]

set_case_analysis 1 config_w[0]
set_case_analysis 1 mac/config_w[0]

#
#

# weight-only data-gated mult registers

set_case_analysis 0 mac/mult_accu_reg[0]/q
set_case_analysis 0 mac/mult_accu_reg[1]/q
set_case_analysis 0 mac/mult_accu_reg[2]/q
set_case_analysis 0 mac/mult_accu_reg[3]/q
set_case_analysis 0 mac/mult_accu_reg[4]/q
set_case_analysis 0 mac/mult_accu_reg[5]/q

# weight-only data-gated output registers

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q

