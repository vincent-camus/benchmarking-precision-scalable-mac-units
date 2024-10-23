##-----------------------------------------------------
## Author:    Vincent Camus, Linyan Mei
## File Name: mac_bfusion_1.sdc
## Function:  SDC constraints for 1-level scalable mac_bfusion
## Notes:     5-mode
## Version:   2.0
##-----------------------------------------------------


############## CREATE MODES ###############

create_mode -name {8b_8b 4b_4b 2b_2b 8b_4b 8b_2b}

############### 8-BIT MODE ################

set_constraint_mode 8b_8b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 0 mode
set_case_analysis 0 mac/mode

# z accu

# (not gated in this mode)

# w input

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
set_case_analysis 0 mac/a[8]
set_case_analysis 0 mac/a[9]
set_case_analysis 0 mac/a[10]
set_case_analysis 0 mac/a[11]
set_case_analysis 0 mac/a[12]
set_case_analysis 0 mac/a[13]
set_case_analysis 0 mac/a[14]
set_case_analysis 0 mac/a[15]

############### 4-BIT MODE ################

set_constraint_mode 4b_4b
create_clock -name "clk" -period $CLK_4B [get_ports clk]

# config

set_case_analysis 1 mode
set_case_analysis 1 mac/mode

# z accu

# by mode
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]
# by data-gated a
set_case_analysis 0 z[0]
set_case_analysis 0 z[1]
set_case_analysis 0 z[2]
set_case_analysis 0 z[3]
set_case_analysis 0 mac/z[0]
set_case_analysis 0 mac/z[1]
set_case_analysis 0 mac/z[2]
set_case_analysis 0 mac/z[3]

# w input by data gating

# (not gated in this mode)

# a inputs

# by data-gated a
set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]
set_case_analysis 0 mac/a[0]
set_case_analysis 0 mac/a[1]
set_case_analysis 0 mac/a[2]
set_case_analysis 0 mac/a[3]
set_case_analysis 0 a[8]
set_case_analysis 0 a[9]
set_case_analysis 0 a[10]
set_case_analysis 0 a[11]
set_case_analysis 0 mac/a[8]
set_case_analysis 0 mac/a[9]
set_case_analysis 0 mac/a[10]
set_case_analysis 0 mac/a[11]

############### 2-BIT MODE ################

set_constraint_mode 2b_2b
create_clock -name "clk" -period $CLK_2B [get_ports clk]

# config

set_case_analysis 1 mode
set_case_analysis 1 mac/mode

# z accu

# by mode
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]
# by data-gated a
set_case_analysis 0 z[0]
set_case_analysis 0 z[1]
set_case_analysis 0 z[2]
set_case_analysis 0 z[3]
set_case_analysis 0 z[4]
set_case_analysis 0 z[5]
set_case_analysis 0 z[6]
set_case_analysis 0 z[7]
set_case_analysis 0 mac/z[0]
set_case_analysis 0 mac/z[1]
set_case_analysis 0 mac/z[2]
set_case_analysis 0 mac/z[3]
set_case_analysis 0 mac/z[4]
set_case_analysis 0 mac/z[5]
set_case_analysis 0 mac/z[6]
set_case_analysis 0 mac/z[7]

# w input

# (not gated in this mode)

# a inputs

# by data-gated a
set_case_analysis 0 a[0]
set_case_analysis 0 a[1]
set_case_analysis 0 a[2]
set_case_analysis 0 a[3]
set_case_analysis 0 a[4]
set_case_analysis 0 a[5]
set_case_analysis 0 mac/a[0]
set_case_analysis 0 mac/a[1]
set_case_analysis 0 mac/a[2]
set_case_analysis 0 mac/a[3]
set_case_analysis 0 mac/a[4]
set_case_analysis 0 mac/a[5]
set_case_analysis 0 a[8]
set_case_analysis 0 a[9]
set_case_analysis 0 a[10]
set_case_analysis 0 a[11]
set_case_analysis 0 a[12]
set_case_analysis 0 a[13]
set_case_analysis 0 mac/a[8]
set_case_analysis 0 mac/a[9]
set_case_analysis 0 mac/a[10]
set_case_analysis 0 mac/a[11]
set_case_analysis 0 mac/a[12]
set_case_analysis 0 mac/a[13]

######### WEIGHT-ONLY 4-BIT MODE ##########

set_constraint_mode 8b_4b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 1 mode
set_case_analysis 1 mac/mode

# z accu

# by mode
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]

# w inputs

# (not gated in this mode)

# a inputs

# (not gated in this mode) 

######### WEIGHT-ONLY 2-BIT MODE ##########

set_constraint_mode 8b_2b
create_clock -name "clk" -period $CLK_8B [get_ports clk]

# config

set_case_analysis 1 mode
set_case_analysis 1 mac/mode

# z accu

# by mode
set_case_analysis 0 z[17]
set_case_analysis 0 z[18]
set_case_analysis 0 z[19]
set_case_analysis 0 mac/z[17]
set_case_analysis 0 mac/z[18]
set_case_analysis 0 mac/z[19]
# by data-gated w
set_case_analysis 0 z[0]
set_case_analysis 0 z[1]
set_case_analysis 0 mac/z[0]
set_case_analysis 0 mac/z[1]

# w inputs

# by data gating
set_case_analysis 0 w[0]
set_case_analysis 0 w[1]
set_case_analysis 0 mac/w[0]
set_case_analysis 0 mac/w[1]
set_case_analysis 0 w[4]
set_case_analysis 0 w[5]
set_case_analysis 0 mac/w[4]
set_case_analysis 0 mac/w[5]

# a inputs

# (not gated in this mode)
