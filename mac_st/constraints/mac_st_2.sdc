##-----------------------------------------------------
## Author:    Linyan Mei
## Function:  SDC constraints for 2-level scalable top_mac_st
## Version:   1.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b 4b 2b}

############### 8-BIT MODE ################

set_constraint_mode 8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 0 config_aw[1]
set_case_analysis 0 config_aw[0]

# z accu

# (not gated in this mode)

############### 4-BIT MODE ################

set_constraint_mode 4b
create_clock -name "clk" -period $CLK_4B [get_ports clk]

# config

set_case_analysis 0 config_aw[1]
set_case_analysis 1 config_aw[0]

# z accu

set_case_analysis 0 mac/z_reg[19]/q
set_case_analysis 0 mac/z_reg[18]/q
set_case_analysis 0 mac/z_reg[17]/q
set_case_analysis 0 mac/z_reg[16]/q

set_case_analysis 0 mac/z_reg[15]/q
set_case_analysis 0 mac/z_reg[14]/q
set_case_analysis 0 mac/z_reg[13]/q
set_case_analysis 0 mac/z_reg[12]/q

set_case_analysis 0 mac/mult_reg[15]/q
set_case_analysis 0 mac/mult_reg[14]/q
set_case_analysis 0 mac/mult_reg[13]/q
set_case_analysis 0 mac/mult_reg[12]/q

set_case_analysis 0 mac/mult_reg[11]/q
set_case_analysis 0 mac/mult_reg[10]/q
set_case_analysis 0 mac/mult_reg[9]/q

############### 2-BIT MODE ################

set_constraint_mode 2b
create_clock -name "clk" -period $CLK_2B [get_ports clk]

# config

set_case_analysis 1 config_aw[1]
set_case_analysis 1 config_aw[0]

# z accu

set_case_analysis 0 mac/z_reg[19]/q
set_case_analysis 0 mac/z_reg[18]/q
set_case_analysis 0 mac/z_reg[17]/q
set_case_analysis 0 mac/z_reg[16]/q

set_case_analysis 0 mac/z_reg[15]/q
set_case_analysis 0 mac/z_reg[14]/q
set_case_analysis 0 mac/z_reg[13]/q
set_case_analysis 0 mac/z_reg[12]/q

set_case_analysis 0 mac/z_reg[11]/q
set_case_analysis 0 mac/z_reg[10]/q
set_case_analysis 0 mac/z_reg[9]/q
set_case_analysis 0 mac/z_reg[8]/q

set_case_analysis 0 mac/mult_reg[15]/q
set_case_analysis 0 mac/mult_reg[14]/q
set_case_analysis 0 mac/mult_reg[13]/q
set_case_analysis 0 mac/mult_reg[12]/q

set_case_analysis 0 mac/mult_reg[11]/q
set_case_analysis 0 mac/mult_reg[10]/q
set_case_analysis 0 mac/mult_reg[9]/q

set_case_analysis 0 mac/mult_reg[8]/q
set_case_analysis 0 mac/mult_reg[7]/q
set_case_analysis 0 mac/mult_reg[6]/q
