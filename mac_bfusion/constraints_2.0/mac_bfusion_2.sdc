##-----------------------------------------------------
## Author:    Vincent Camus, Linyan Mei
## File Name: mac_bfusion_2.sdc
## Function:  SDC constraints for 2-level scalable mac_bfusion
## Notes:     5-mode
## Version:   2.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 0 config_aw[2]
set_case_analysis 0 config_aw[1]
set_case_analysis 0 config_aw[0]
set_case_analysis 0 mac/config_aw[2]
set_case_analysis 0 mac/config_aw[1]
set_case_analysis 0 mac/config_aw[0]

# z accu

# (not gated in this mode)

# a inputs

set_case_analysis 0 a[8]
set_case_analysis 0 a[9]
set_case_analysis 0 a[10]
set_case_analysis 0 a[11]
set_case_analysis 0 a[12]
set_case_analysis 0 a[13]
set_case_analysis 0 a[14]
set_case_analysis 0 a[15]
set_case_analysis 0 a[16]
set_case_analysis 0 a[17]
set_case_analysis 0 a[18]
set_case_analysis 0 a[19]
set_case_analysis 0 a[20]
set_case_analysis 0 a[21]
set_case_analysis 0 a[22]
set_case_analysis 0 a[23]
set_case_analysis 0 a[24]
set_case_analysis 0 a[25]
set_case_analysis 0 a[26]
set_case_analysis 0 a[27]
set_case_analysis 0 a[28]
set_case_analysis 0 a[29]
set_case_analysis 0 a[30]
set_case_analysis 0 a[31]
set_case_analysis 0 mac/a[8]
set_case_analysis 0 mac/a[9]
set_case_analysis 0 mac/a[10]
set_case_analysis 0 mac/a[11]
set_case_analysis 0 mac/a[12]
set_case_analysis 0 mac/a[13]
set_case_analysis 0 mac/a[14]
set_case_analysis 0 mac/a[15]
set_case_analysis 0 mac/a[16]
set_case_analysis 0 mac/a[17]
set_case_analysis 0 mac/a[18]
set_case_analysis 0 mac/a[19]
set_case_analysis 0 mac/a[20]
set_case_analysis 0 mac/a[21]
set_case_analysis 0 mac/a[22]
set_case_analysis 0 mac/a[23]
set_case_analysis 0 mac/a[24]
set_case_analysis 0 mac/a[25]
set_case_analysis 0 mac/a[26]
set_case_analysis 0 mac/a[27]
set_case_analysis 0 mac/a[28]
set_case_analysis 0 mac/a[29]
set_case_analysis 0 mac/a[30]
set_case_analysis 0 mac/a[31]

# w input

set_case_analysis 0 w[8]
set_case_analysis 0 w[9]
set_case_analysis 0 w[10]
set_case_analysis 0 w[11]
set_case_analysis 0 w[12]
set_case_analysis 0 w[13]
set_case_analysis 0 w[14]
set_case_analysis 0 w[15]
set_case_analysis 0 w[16]
set_case_analysis 0 w[17]
set_case_analysis 0 w[18]
set_case_analysis 0 w[19]
set_case_analysis 0 w[20]
set_case_analysis 0 w[21]
set_case_analysis 0 w[22]
set_case_analysis 0 w[23]
set_case_analysis 0 w[24]
set_case_analysis 0 w[25]
set_case_analysis 0 w[26]
set_case_analysis 0 w[27]
set_case_analysis 0 w[28]
set_case_analysis 0 w[29]
set_case_analysis 0 w[30]
set_case_analysis 0 w[31]
set_case_analysis 0 mac/w[8]
set_case_analysis 0 mac/w[9]
set_case_analysis 0 mac/w[10]
set_case_analysis 0 mac/w[11]
set_case_analysis 0 mac/w[12]
set_case_analysis 0 mac/w[13]
set_case_analysis 0 mac/w[14]
set_case_analysis 0 mac/w[15]
set_case_analysis 0 mac/w[16]
set_case_analysis 0 mac/w[17]
set_case_analysis 0 mac/w[18]
set_case_analysis 0 mac/w[19]
set_case_analysis 0 mac/w[20]
set_case_analysis 0 mac/w[21]
set_case_analysis 0 mac/w[22]
set_case_analysis 0 mac/w[23]
set_case_analysis 0 mac/w[24]
set_case_analysis 0 mac/w[25]
set_case_analysis 0 mac/w[26]
set_case_analysis 0 mac/w[27]
set_case_analysis 0 mac/w[28]
set_case_analysis 0 mac/w[29]
set_case_analysis 0 mac/w[30]
set_case_analysis 0 mac/w[31]

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk]

# config

set_case_analysis 0 config_aw[2]
set_case_analysis 1 config_aw[1]
set_case_analysis 0 config_aw[0]
set_case_analysis 0 mac/config_aw[2]
set_case_analysis 1 mac/config_aw[1]
set_case_analysis 0 mac/config_aw[0]

# z accu

set_case_analysis 0 z[14]
set_case_analysis 0 z[15]
set_case_analysis 0 z[16]
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[14]
set_case_analysis 0 mac/z[15]
set_case_analysis 0 mac/z[16]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]

# a inputs

set_case_analysis 0 a[16]
set_case_analysis 0 a[17]
set_case_analysis 0 a[18]
set_case_analysis 0 a[19]
set_case_analysis 0 a[20]
set_case_analysis 0 a[21]
set_case_analysis 0 a[22]
set_case_analysis 0 a[23]
set_case_analysis 0 a[24]
set_case_analysis 0 a[25]
set_case_analysis 0 a[26]
set_case_analysis 0 a[27]
set_case_analysis 0 a[28]
set_case_analysis 0 a[29]
set_case_analysis 0 a[30]
set_case_analysis 0 a[31]
set_case_analysis 0 mac/a[16]
set_case_analysis 0 mac/a[17]
set_case_analysis 0 mac/a[18]
set_case_analysis 0 mac/a[19]
set_case_analysis 0 mac/a[20]
set_case_analysis 0 mac/a[21]
set_case_analysis 0 mac/a[22]
set_case_analysis 0 mac/a[23]
set_case_analysis 0 mac/a[24]
set_case_analysis 0 mac/a[25]
set_case_analysis 0 mac/a[26]
set_case_analysis 0 mac/a[27]
set_case_analysis 0 mac/a[28]
set_case_analysis 0 mac/a[29]
set_case_analysis 0 mac/a[30]
set_case_analysis 0 mac/a[31]

# w input

set_case_analysis 0 w[16]
set_case_analysis 0 w[17]
set_case_analysis 0 w[18]
set_case_analysis 0 w[19]
set_case_analysis 0 w[20]
set_case_analysis 0 w[21]
set_case_analysis 0 w[22]
set_case_analysis 0 w[23]
set_case_analysis 0 w[24]
set_case_analysis 0 w[25]
set_case_analysis 0 w[26]
set_case_analysis 0 w[27]
set_case_analysis 0 w[28]
set_case_analysis 0 w[29]
set_case_analysis 0 w[30]
set_case_analysis 0 w[31]
set_case_analysis 0 mac/w[16]
set_case_analysis 0 mac/w[17]
set_case_analysis 0 mac/w[18]
set_case_analysis 0 mac/w[19]
set_case_analysis 0 mac/w[20]
set_case_analysis 0 mac/w[21]
set_case_analysis 0 mac/w[22]
set_case_analysis 0 mac/w[23]
set_case_analysis 0 mac/w[24]
set_case_analysis 0 mac/w[25]
set_case_analysis 0 mac/w[26]
set_case_analysis 0 mac/w[27]
set_case_analysis 0 mac/w[28]
set_case_analysis 0 mac/w[29]
set_case_analysis 0 mac/w[30]
set_case_analysis 0 mac/w[31]

############### 2-BIT MODE ################

set_constraint_mode 2b_2b
create_clock -name "clk" -period $CLK_2B [get_ports clk]

# config

set_case_analysis 0 config_aw[2]
set_case_analysis 1 config_aw[1]
set_case_analysis 1 config_aw[0]
set_case_analysis 0 mac/config_aw[2]
set_case_analysis 1 mac/config_aw[1]
set_case_analysis 1 mac/config_aw[0]

# z accu

set_case_analysis 0 z[12]
set_case_analysis 0 z[13]
set_case_analysis 0 z[14]
set_case_analysis 0 z[15]
set_case_analysis 0 z[16]
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[12]
set_case_analysis 0 mac/z[13]
set_case_analysis 0 mac/z[14]
set_case_analysis 0 mac/z[15]
set_case_analysis 0 mac/z[16]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]

# a inputs

# (not gated in this mode)

# w input

# (not gated in this mode)

######### WEIGHT-ONLY 4-BIT MODE ##########

set_constraint_mode 8b_4b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 1 config_aw[2]
set_case_analysis 1 config_aw[1]
set_case_analysis 0 config_aw[0]
set_case_analysis 1 mac/config_aw[2]
set_case_analysis 1 mac/config_aw[1]
set_case_analysis 0 mac/config_aw[0]

# z accu

set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]

# a inputs

set_case_analysis 0 a[16]
set_case_analysis 0 a[17]
set_case_analysis 0 a[18]
set_case_analysis 0 a[19]
set_case_analysis 0 a[20]
set_case_analysis 0 a[21]
set_case_analysis 0 a[22]
set_case_analysis 0 a[23]
set_case_analysis 0 a[24]
set_case_analysis 0 a[25]
set_case_analysis 0 a[26]
set_case_analysis 0 a[27]
set_case_analysis 0 a[28]
set_case_analysis 0 a[29]
set_case_analysis 0 a[30]
set_case_analysis 0 a[31]
set_case_analysis 0 mac/a[16]
set_case_analysis 0 mac/a[17]
set_case_analysis 0 mac/a[18]
set_case_analysis 0 mac/a[19]
set_case_analysis 0 mac/a[20]
set_case_analysis 0 mac/a[21]
set_case_analysis 0 mac/a[22]
set_case_analysis 0 mac/a[23]
set_case_analysis 0 mac/a[24]
set_case_analysis 0 mac/a[25]
set_case_analysis 0 mac/a[26]
set_case_analysis 0 mac/a[27]
set_case_analysis 0 mac/a[28]
set_case_analysis 0 mac/a[29]
set_case_analysis 0 mac/a[30]
set_case_analysis 0 mac/a[31]

# w input

set_case_analysis 0 w[8]
set_case_analysis 0 w[9]
set_case_analysis 0 w[10]
set_case_analysis 0 w[11]
set_case_analysis 0 w[12]
set_case_analysis 0 w[13]
set_case_analysis 0 w[14]
set_case_analysis 0 w[15]
set_case_analysis 0 w[16]
set_case_analysis 0 w[17]
set_case_analysis 0 w[18]
set_case_analysis 0 w[19]
set_case_analysis 0 w[20]
set_case_analysis 0 w[21]
set_case_analysis 0 w[22]
set_case_analysis 0 w[23]
set_case_analysis 0 w[24]
set_case_analysis 0 w[25]
set_case_analysis 0 w[26]
set_case_analysis 0 w[27]
set_case_analysis 0 w[28]
set_case_analysis 0 w[29]
set_case_analysis 0 w[30]
set_case_analysis 0 w[31]
set_case_analysis 0 mac/w[8]
set_case_analysis 0 mac/w[9]
set_case_analysis 0 mac/w[10]
set_case_analysis 0 mac/w[11]
set_case_analysis 0 mac/w[12]
set_case_analysis 0 mac/w[13]
set_case_analysis 0 mac/w[14]
set_case_analysis 0 mac/w[15]
set_case_analysis 0 mac/w[16]
set_case_analysis 0 mac/w[17]
set_case_analysis 0 mac/w[18]
set_case_analysis 0 mac/w[19]
set_case_analysis 0 mac/w[20]
set_case_analysis 0 mac/w[21]
set_case_analysis 0 mac/w[22]
set_case_analysis 0 mac/w[23]
set_case_analysis 0 mac/w[24]
set_case_analysis 0 mac/w[25]
set_case_analysis 0 mac/w[26]
set_case_analysis 0 mac/w[27]
set_case_analysis 0 mac/w[28]
set_case_analysis 0 mac/w[29]
set_case_analysis 0 mac/w[30]
set_case_analysis 0 mac/w[31]

######### WEIGHT-ONLY 2-BIT MODE ##########

set_constraint_mode 8b_2b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 1 config_aw[2]
set_case_analysis 1 config_aw[1]
set_case_analysis 1 config_aw[0]
set_case_analysis 1 mac/config_aw[2]
set_case_analysis 1 mac/config_aw[1]
set_case_analysis 1 mac/config_aw[0]

# z accu

set_case_analysis 0 z[16]
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[16]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]

# a inputs

# (not gated in this mode)

# w input

set_case_analysis 0 w[8]
set_case_analysis 0 w[9]
set_case_analysis 0 w[10]
set_case_analysis 0 w[11]
set_case_analysis 0 w[12]
set_case_analysis 0 w[13]
set_case_analysis 0 w[14]
set_case_analysis 0 w[15]
set_case_analysis 0 w[16]
set_case_analysis 0 w[17]
set_case_analysis 0 w[18]
set_case_analysis 0 w[19]
set_case_analysis 0 w[20]
set_case_analysis 0 w[21]
set_case_analysis 0 w[22]
set_case_analysis 0 w[23]
set_case_analysis 0 w[24]
set_case_analysis 0 w[25]
set_case_analysis 0 w[26]
set_case_analysis 0 w[27]
set_case_analysis 0 w[28]
set_case_analysis 0 w[29]
set_case_analysis 0 w[30]
set_case_analysis 0 w[31]
set_case_analysis 0 mac/w[8]
set_case_analysis 0 mac/w[9]
set_case_analysis 0 mac/w[10]
set_case_analysis 0 mac/w[11]
set_case_analysis 0 mac/w[12]
set_case_analysis 0 mac/w[13]
set_case_analysis 0 mac/w[14]
set_case_analysis 0 mac/w[15]
set_case_analysis 0 mac/w[16]
set_case_analysis 0 mac/w[17]
set_case_analysis 0 mac/w[18]
set_case_analysis 0 mac/w[19]
set_case_analysis 0 mac/w[20]
set_case_analysis 0 mac/w[21]
set_case_analysis 0 mac/w[22]
set_case_analysis 0 mac/w[23]
set_case_analysis 0 mac/w[24]
set_case_analysis 0 mac/w[25]
set_case_analysis 0 mac/w[26]
set_case_analysis 0 mac/w[27]
set_case_analysis 0 mac/w[28]
set_case_analysis 0 mac/w[29]
set_case_analysis 0 mac/w[30]
set_case_analysis 0 mac/w[31]
