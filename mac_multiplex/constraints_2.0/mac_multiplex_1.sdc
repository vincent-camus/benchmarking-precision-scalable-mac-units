##-----------------------------------------------------
## Author:    Vincent Camus
## File Name: mac_multiplex_1.sdc
## Function:  SDC constraints for mac_multiplex with CONFIG_AW_WIDTH=1
## Notes:     5-mode
## Version:   2.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 0 config_aw[0]
# (not implemented)

set_case_analysis 0 mac/config_aw[0]
# (not implemented)

# z accu

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

set_case_analysis 0 mac/z_reg[8]/q
set_case_analysis 0 mac/z_reg[9]/q
set_case_analysis 0 mac/z_reg[10]/q
set_case_analysis 0 mac/z_reg[11]/q

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk]

# config

set_case_analysis 1 config_aw[0]
# (not implemented)

set_case_analysis 1 mac/config_aw[0]
# (not implemented)

# z accu

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

# (z_reg[8]  not gated in this mode)
# (z_reg[9]  not gated in this mode)
# (z_reg[10] not gated in this mode)
# (z_reg[11] not gated in this mode)

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

############### 2-BIT MODE ################

set_constraint_mode 2b_2b
create_clock -name "clk" -period $CLK_2B [get_ports clk]

# config

set_case_analysis 1 config_aw[0]
# (not implemented)

set_case_analysis 1 mac/config_aw[0]
# (not implemented)

# z accu

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

# (z_reg[8]  not gated in this mode)
# (z_reg[9]  not gated in this mode)
# (z_reg[10] not gated in this mode)
# (z_reg[11] not gated in this mode)

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

# symmetrically data-gated inputs

set_case_analysis 0 w[0]
set_case_analysis 0 a[0]
set_case_analysis 0 w[1]
set_case_analysis 0 a[1]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/a[0]
set_case_analysis 0 mac/w[1]
set_case_analysis 0 mac/a[1]

set_case_analysis 0 w[4]
set_case_analysis 0 a[4]
set_case_analysis 0 w[5]
set_case_analysis 0 a[5]
set_case_analysis 0 mac/w[4]
set_case_analysis 0 mac/a[4]
set_case_analysis 0 mac/w[5]
set_case_analysis 0 mac/a[5]

# symmetrically data-gated mult register (!!! compensation: 1 for last bit !!!)

set_case_analysis 0 mac/mult_reg[0]/q
set_case_analysis 0 mac/mult_reg[1]/q
set_case_analysis 0 mac/mult_reg[2]/q
set_case_analysis 1 mac/mult_reg[3]/q

set_case_analysis 0 mac/mult_reg[8]/q
set_case_analysis 0 mac/mult_reg[9]/q
set_case_analysis 0 mac/mult_reg[10]/q
set_case_analysis 1 mac/mult_reg[11]/q

# symmetrically data-gated accumulator

set_case_analysis 0 mac/z_reg[0]/q
set_case_analysis 0 mac/z_reg[1]/q
set_case_analysis 0 mac/z_reg[2]/q
set_case_analysis 0 mac/z_reg[3]/q

set_case_analysis 0 mac/z_reg[12]/q
set_case_analysis 0 mac/z_reg[13]/q
set_case_analysis 0 mac/z_reg[14]/q
set_case_analysis 0 mac/z_reg[15]/q

######### WEIGHT-ONLY 4-BIT MODE ##########

set_constraint_mode 8b_4b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 0 config_aw[0]
# (not implemented)

set_case_analysis 0 mac/config_aw[0]
# (not implemented)

# z accu

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

set_case_analysis 0 mac/z_reg[8]/q
set_case_analysis 0 mac/z_reg[9]/q
set_case_analysis 0 mac/z_reg[10]/q
set_case_analysis 0 mac/z_reg[11]/q

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

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

# config

set_case_analysis 0 config_aw[0]
# (not implemented)

set_case_analysis 0 mac/config_aw[0]
# (not implemented)

# z accu

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

set_case_analysis 0 mac/z_reg[8]/q
set_case_analysis 0 mac/z_reg[9]/q
set_case_analysis 0 mac/z_reg[10]/q
set_case_analysis 0 mac/z_reg[11]/q

# (not implemented)
# (not implemented)
# (not implemented)
# (not implemented)

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
