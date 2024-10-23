##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: mac_conventional.sdc
## Function:  SDC constraints for mac_conventional
## Notes:     STA considering symmetric data-gating only
## Version:   1.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b 4b 2b}

############### 8-BIT MODE ################

set_constraint_mode 8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

############### 4-BIT MODE ################

set_constraint_mode 4b
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

set_constraint_mode 2b
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
