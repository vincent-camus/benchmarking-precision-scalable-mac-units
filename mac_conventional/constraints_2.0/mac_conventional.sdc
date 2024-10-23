##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: mac_conventional.sdc
## Function:  SDC constraints for mac_conventional
## Notes:     5-mode
## Version:   2.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk]

# symmetrically data-gated inputs

set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 w[2]
set_case_analysis 0 w[3]

set_case_analysis 0 a_reg_reg[0]/q
set_case_analysis 0 a_reg_reg[1]/q
set_case_analysis 0 a_reg_reg[2]/q
set_case_analysis 0 a_reg_reg[3]/q

set_case_analysis 0 w_reg_reg[0]/q
set_case_analysis 0 w_reg_reg[1]/q
set_case_analysis 0 w_reg_reg[2]/q
set_case_analysis 0 w_reg_reg[3]/q

# symmetrically data-gated mult register

set_case_analysis 0 mac/mult_reg[0]/q
set_case_analysis 0 mac/mult_reg[1]/q
set_case_analysis 0 mac/mult_reg[2]/q
set_case_analysis 0 mac/mult_reg[3]/q
set_case_analysis 0 mac/mult_reg[4]/q
set_case_analysis 0 mac/mult_reg[5]/q
set_case_analysis 0 mac/mult_reg[6]/q
set_case_analysis 0 mac/mult_reg[7]/q

# symmetrically data-gated accumulator

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
create_clock -name "clk" -period $CLK_2B [get_ports clk]

# symmetrically data-gated inputs

set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]
set_case_analysis 0 a[4]
set_case_analysis 0 a[5]

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 w[2]
set_case_analysis 0 w[3]
set_case_analysis 0 w[4]
set_case_analysis 0 w[5]

set_case_analysis 0 a_reg_reg[0]/q
set_case_analysis 0 a_reg_reg[1]/q
set_case_analysis 0 a_reg_reg[2]/q
set_case_analysis 0 a_reg_reg[3]/q
set_case_analysis 0 a_reg_reg[4]/q
set_case_analysis 0 a_reg_reg[5]/q

set_case_analysis 0 w_reg_reg[0]/q
set_case_analysis 0 w_reg_reg[1]/q
set_case_analysis 0 w_reg_reg[2]/q
set_case_analysis 0 w_reg_reg[3]/q
set_case_analysis 0 w_reg_reg[4]/q
set_case_analysis 0 w_reg_reg[5]/q

# symmetrically data-gated mult register

set_case_analysis 0 mac/mult_reg[0]/q
set_case_analysis 0 mac/mult_reg[1]/q
set_case_analysis 0 mac/mult_reg[2]/q
set_case_analysis 0 mac/mult_reg[3]/q
set_case_analysis 0 mac/mult_reg[4]/q
set_case_analysis 0 mac/mult_reg[5]/q
set_case_analysis 0 mac/mult_reg[6]/q
set_case_analysis 0 mac/mult_reg[7]/q
set_case_analysis 0 mac/mult_reg[8]/q
set_case_analysis 0 mac/mult_reg[9]/q
set_case_analysis 0 mac/mult_reg[10]/q
set_case_analysis 0 mac/mult_reg[11]/q

# symmetrically data-gated accumulator

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
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# weight-only data-gated inputs

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 w[2]
set_case_analysis 0 w[3]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/w[1]
set_case_analysis 0 mac/w[2]
set_case_analysis 0 mac/w[3]

# weight-only data-gated mult register (TO CHECK: NO COMPENSATION???)

set_case_analysis 0 mac/mult_reg[0]/q
set_case_analysis 0 mac/mult_reg[1]/q
set_case_analysis 0 mac/mult_reg[2]/q
set_case_analysis 0 mac/mult_reg[3]/q

# weight-only data-gated accumulator

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q

######### WEIGHT-ONLY 2-BIT MODE ##########

set_constraint_mode 8b_2b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# weight-only data-gated inputs

set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 w[2]
set_case_analysis 0 w[3]
set_case_analysis 0 w[4]
set_case_analysis 0 w[5]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/w[1]
set_case_analysis 0 mac/w[2]
set_case_analysis 0 mac/w[3]
set_case_analysis 0 mac/w[4]
set_case_analysis 0 mac/w[5]

# weight-only data-gated mult register (TO CHECK: NO COMPENSATION???)

set_case_analysis 0 mac/mult_reg[0]/q
set_case_analysis 0 mac/mult_reg[1]/q
set_case_analysis 0 mac/mult_reg[2]/q
set_case_analysis 0 mac/mult_reg[3]/q
set_case_analysis 0 mac/mult_reg[4]/q
set_case_analysis 0 mac/mult_reg[5]/q

# weight-only data-gated accumulator

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q
set_case_analysis 0 mac/z_reg[4]/q
set_case_analysis 0 mac/z_reg[5]/q
