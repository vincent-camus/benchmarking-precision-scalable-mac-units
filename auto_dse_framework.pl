#!/usr/bin/perl -w
##-----------------------------------------------------
## Author:    Vincent Camus
## Function:  automatic DSE framework for precision-scalable MACs
## Version:   2.0
## Notes:     DVFS, 5-mode, 3-clock, asymmetric measure,
##            added design space limitation
##-----------------------------------------------------


use warnings;
use strict;
use Parallel::ForkManager;
use YAML::Tiny;
use Sys::Hostname qw(hostname);
use Time::localtime qw(localtime);
use Tie::IxHash;
use Fcntl qw(:flock SEEK_END);
use IO::Handle;
use List::Util qw(max min);
use File::Path qw(make_path);

#################################### Design parameters

# Design name
my $DESIGN         = "mac_multiplex";

# Clock delays (ns)
my $CLK_MIN        = 0.15;
my $CLK_MAX        = 1.25;
my $CLK_STEP       = 0.05;

# Design/script versions
my $BATCH_VERSION  = "1.0";
my $SDC_VERSION    = "2.0";   # 5 modes, 3 clocks
my $ASSERT_VERSION = "1.0";
my $RTL_VERSION    = "1.1";   # external clock gating
my $TB_VERSION     = "1.0";
my $PB_VERSION     = "1.0.1"; # clean-up
my $SYN_VERSION    = "2.0";   # DVFS
my $SIM_PB_VERSION = "2.0";   # DVFS

# Other parameters
my $TIMING_MARGIN  = 0.010;   # 0.010 ns as standard
my $LIB_V          = "/scratch/camus/common/dkits/tcbn28hpmbwp35.v";
my $LIB_DB_HIGH    = "/scratch/camus/common/dkits/tcbn28hpmbwp35tt1v25c_ccs.lib";
my $LIB_DB         = "/scratch/camus/common/dkits/tcbn28hpmbwp35tt0p9v25c_ccs.lib";
my $LIB_DB_LOW     = "/scratch/camus/common/dkits/tcbn28hpmbwp35tt0p8v25c_ccs.lib";

# Design notes (written on reports)
my $NOTE           = "";

#################################### Script setup

# Home directory
my $MAIN_DIR    = "/home/camus/multi-precision-mac/auto";
my $SCRATCH_DIR = "/scratch/camus/multi-precision-mac";

# Design/script versions
my $REPORT_DIR  = "$MAIN_DIR/results/reports_$DESIGN".($NOTE ne "" ? "_$NOTE" : "");
my $EXPORT_DIR  = "$SCRATCH_DIR/exports_$DESIGN".($NOTE ne "" ? "_$NOTE" : "");

# Result file
my $RESULT_FILE = "$MAIN_DIR/results/results_$DESIGN".($NOTE ne "" ? "_$NOTE" : "").".csv";

# Script directories
my $BATCH_DIR   = "$MAIN_DIR/$DESIGN/batch_$BATCH_VERSION";
my $SDC_DIR     = "$MAIN_DIR/$DESIGN/constraints_$SDC_VERSION";
my $ASSERT_DIR  = "$MAIN_DIR/$DESIGN/assertions_$ASSERT_VERSION";

# Script files
my $RTL_FILE    = "$MAIN_DIR/$DESIGN/${DESIGN}_$RTL_VERSION.sv";
my $PB_FILE     = "$MAIN_DIR/$DESIGN/pb_${DESIGN}_$PB_VERSION.sv";
my $SYN_FILE    = "$MAIN_DIR/$DESIGN/syn_${DESIGN}_$SYN_VERSION.tcl";
my $SIM_PB_FILE = "$MAIN_DIR/$DESIGN/sim_pb_${DESIGN}_$SIM_PB_VERSION.tcl";

# Verbose mode
my $log = 1;

# Fork management
my $YAML_CONF_FILE = "/home/camus/mthread_conf.yml";

# Master script setup
$0 = "mac_master";
$| = 0;

# Fix config parameters
(my $host = hostname) =~ s/\.\S*$//;
my $physical_threads = 8;
$physical_threads = 16 if $host =~ m/iclabsrv3|tclhs1/;

# Fork setup
my $max_threads = 1;
my $pm = Parallel::ForkManager->new($max_threads);

# YAML database setup
my $conf = "";
my ($mode,$nice_value,$verbose,$day_threads,$night_threads,$night_start,$day_start,$thread_mode,$thread_leave,$update_delay);
my $yaml = YAML::Tiny->new;

#################################### Subroutines

# File locking subroutines
sub lock   {
	my ($fh) = @_;
	flock($fh, LOCK_EX) or die $!;
	seek($fh, 0, SEEK_END) or die $!;
}
sub unlock {
	my ($fh) = @_;
	flock($fh, LOCK_UN) or die $!;
}

# Print subroutines
sub print_info    { print "\033\[100;97;1mINFO: $_[0]\033\[0m\n" if ($verbose >= 1); }
sub print_skip    { print "\033\[104;97;1mSKIP: $_[0]\033\[0m\n" if ($verbose >= 1); }
sub print_proc    { print "\033\[44;97;1mPROC: $_[0]\033\[0m\n";     }
sub print_warning { print "\033\[103;30;1mWARNING: $_[0]\033\[0m\n"; }
sub print_error   { print "\033\[41;97;1mERROR: $_[0]\033\[0m\n";    }

# Other subroutines
sub uniq { my %seen; grep !$seen{$_}++, @_; }

# YAML configuration update subroutine
sub conf_update {
	$yaml = YAML::Tiny->read($YAML_CONF_FILE) or 0;
	$mode          = $yaml->[0]->{mode}->{$host}          || $yaml->[0]->{mode}->{others}          || "STOP";
	$nice_value    = $yaml->[0]->{nice_value}->{$host}    || $yaml->[0]->{nice_value}->{others}    || 0;
	$verbose       = $yaml->[0]->{verbose}->{$host}       || $yaml->[0]->{verbose}->{others}       || 0;
	$day_threads   = $yaml->[0]->{day_threads}->{$host}   || $yaml->[0]->{day_threads}->{others}   || 0;
	$night_threads = $yaml->[0]->{night_threads}->{$host} || $yaml->[0]->{night_threads}->{others} || 0;
	$night_start   = $yaml->[0]->{night_start}->{$host}   || $yaml->[0]->{night_start}->{others}   || "18:00";
	$day_start     = $yaml->[0]->{day_start}->{$host}     || $yaml->[0]->{day_start}->{others}     || "8:00";
	$thread_mode   = $yaml->[0]->{thread_mode}->{$host}   || $yaml->[0]->{thread_mode}->{others}   || "FIXED";
	$thread_leave  = $yaml->[0]->{thread_leave}->{$host}  || $yaml->[0]->{thread_leave}->{others}  || 16;
	$update_delay  = $yaml->[0]->{update_delay}->{$host}  || $yaml->[0]->{update_delay}->{others}  || 1;
	if ($conf ne "$mode, $nice_value, $verbose, $day_threads, $night_threads, $night_start, $day_start, $thread_mode, $thread_leave, $update_delay") {
		$conf = "$mode, $nice_value, $verbose, $day_threads, $night_threads, $night_start, $day_start, $thread_mode, $thread_leave, $update_delay";
		print_warning "YAML configuration updated ($conf)";
	}
	my $m   = localtime->min();
	my $h   = localtime->hour();
	my $day = localtime->wday();
	my $now = $m+60*$h;
	$day_start   =~ m/(\d+).?(\d*)/;
	$day_start   = ($2 || 0) + 60*$1;
	$night_start =~ m/(\d+).?(\d*)/;
	$night_start = ($2 || 0) + 60*$1;
	if ($mode eq "RUN") {
		if ($now > $night_start || $now < $day_start || $day == 0 || $day == 6) {
			$max_threads = $night_threads;
		} else {
			$max_threads = $day_threads; 
			if ($thread_mode eq "ADAPTATIVE") {
				my $load = sprintf("%.0f",`uptime | grep -ohe 'load average: [0-9.]*, [0-9.]*' | awk '{ print \$4 }'`); 
				$max_threads = max(min($day_threads,$physical_threads-$load-$thread_leave),1);
				print_warning "YAML configured in adaptative mode: $max_threads = max(min($day_threads,$physical_threads-$load-$thread_leave),1)";
			}
		}
		$pm->set_max_procs($max_threads);
	} else {
		print_warning "auto-exit engaged, waiting for all children...";
		$max_threads = -1;
		$pm->set_max_procs($max_threads);
		$pm->wait_all_children;
		print_warning "script interrupted by auto-exit";
		exit 42;
	}
}

# Auto configuration update subroutine
$SIG{ALRM} = sub { conf_update(); alarm $update_delay*60; };

#################################### Setup processing

# Update configuration and engage auto system
conf_update();
alarm $update_delay*60;

# Get entity list
opendir (DIR, $BATCH_DIR) or die print_error "cannot open batch directory $BATCH_DIR";
my @entity_list = grep(/.*\.sv$/,readdir(DIR));
closedir (DIR);
map { s/\.[^.]+$//; } @entity_list;

# Create output directories
if (!(-d $REPORT_DIR)) {
	make_path $REPORT_DIR or die print_error "cannot create report directory $REPORT_DIR";
	print_info "created report directory $REPORT_DIR";
}
if (!(-d $EXPORT_DIR)) {
make_path $EXPORT_DIR or die print_error "cannot create export directory $EXPORT_DIR";
	print_info "created export directory $EXPORT_DIR";
}
if (!(-d $SCRATCH_DIR)) {
make_path $SCRATCH_DIR or die print_error "cannot create export directory $SCRATCH_DIR";
	print_info "created export directory $SCRATCH_DIR";
}

#################################### Start loops

my $pm_count = 0;

# Loop entity
ENTITY: for my $ENTITY (@entity_list) {
	
# Loop clock delays
CLK_2B: for (my $CLK_2B = $CLK_MIN; $CLK_2B <= $CLK_MAX; $CLK_2B += $CLK_STEP) {
CLK_4B: for (my $CLK_4B = $CLK_2B;  $CLK_4B <= $CLK_MAX; $CLK_4B += $CLK_STEP) {
CLK_8B: for (my $CLK_8B = $CLK_4B;  $CLK_8B <= $CLK_MAX; $CLK_8B += $CLK_STEP) {

	# Design space limitation
    next CLK_8B if ($CLK_8B-$CLK_4B > 0.6);
    next CLK_8B if ($CLK_4B-$CLK_2B > 0.5);
	
	#################################### Start loop processing
	
	# Fullname of entity and clock delays
	my $CLCKS    = sprintf("%.3f-%.3f-%.3f", $CLK_8B, $CLK_4B, $CLK_2B);
	my $FULLNAME = ${ENTITY}."_clks:${CLCKS}".($NOTE ne "" ? ":note:$NOTE" : "");
	my $TMP_DIR  = "$SCRATCH_DIR/tmp_$FULLNAME";
	
	# Check existing before start
	next CLK_8B if (-e "$EXPORT_DIR/$FULLNAME.v");
	next CLK_8B if (-e "$REPORT_DIR/$FULLNAME.rpt");
	next CLK_8B if (-d "$TMP_DIR");
	
	# Wait if max_proc zero
	sleep(60) while ($max_threads == 0);
	
	# Fork
	$pm_count++;
	my $pid = $pm->start($pm_count) and next;
	$0 = "${pm_count}_".($FULLNAME =~ s/:/-/gr);
	setpriority(0,$pid,$nice_value);
	print_proc "$FULLNAME forking child";
	
	# Re-check existing
	$pm->finish(10) if (-e "$EXPORT_DIR/$FULLNAME.v");
	$pm->finish(11) if (-e "$REPORT_DIR/$FULLNAME.rpt");
	$pm->finish(12) if (-d "$TMP_DIR");
	
	#################################### Setup tmp directory
	
	# Setup directory
	mkdir $TMP_DIR or die "Unable to create directory $TMP_DIR\n";
	chdir $TMP_DIR;
	
	# Sourcing
	`ln -s /home/camus/multi-precision-mac/sim/edadk.conf .`;
	
	#################################### Starting report
	
	# Prepare synthesis script
	open rpt_fp, ">$FULLNAME.rpt" or die print_error "$FULLNAME failed to write $FULLNAME.rpt";
	print rpt_fp <<EOF;
############### INFORMATION

NAME         $FULLNAME

CLK_8B       $CLK_8B
CLK_4B       $CLK_4B
CLK_2B       $CLK_2B

BATCH_DIR    $BATCH_DIR
SDC_DIR      $SDC_DIR
ASSERT_DIR   $ASSERT_DIR

RTL_FILE     $RTL_FILE
PB_FILE      $PB_FILE
SYN_FILE     $SYN_FILE
SIM_PB_FILE  $SIM_PB_FILE

LIB_DB       $LIB_DB
LIB_DB_LOW   $LIB_DB_LOW
LIB_DB_HIGH  $LIB_DB_HIGH

NOTE         $NOTE
EOF
	close rpt_fp;
	
	#################################### Synthesis
	
	# Prepare synthesis script
	open syn_fp, ">syn_setup.tcl" or die print_error "$FULLNAME failed to write syn_setup.tcl";
	print syn_fp <<EOF;
############ DESIGN PARAMETERS ############

# Design
set DESIGN       $DESIGN
set RTL_FILE     $RTL_FILE

# Entity
set ENTITY       $ENTITY

# Delays
set CLK_2B       $CLK_2B
set CLK_4B       $CLK_4B
set CLK_8B       $CLK_8B

# Design name
set FULLNAME     $FULLNAME

############ SCRIPT PARAMETERS ############

# Paths
set BATCH_PATH   $BATCH_DIR
set SDC_PATH     $SDC_DIR
set REPORT_PATH  .
set EXPORT_PATH  .

# Libraries
set LIB_DB       $LIB_DB
set LIB_DB_LOW   $LIB_DB_LOW
set LIB_DB_HIGH  $LIB_DB_HIGH

set AUTO         yes
EOF
	close syn_fp;
	
	# Run syn
	print_info "$FULLNAME synthesis";
	my $syn_log = ($verbose < 2 ? " >> syn.log" : "");
	system "tcsh -c 'genus -legacy_ui -batch -f syn_setup.tcl -f $SYN_FILE $syn_log'";
	my $status = system "tail -2 syn.log | grep -q -P 'Abnormal|problems'";
	if ($status == 0) { die print_error "$FULLNAME failed synthesis"; }
	
	#################################### Early result data
	
	# Setup result data
	my %data;
	tie %data, "Tie::IxHash" or die print_error "$FULLNAME could not tie %data hash table";

	# Extract timings
	my $syn_rpt = do {
		local $/;
		open my $syn_rpt_fp, "$FULLNAME.rpt";
		<$syn_rpt_fp>
	} or die "ERROR: Failed to read $FULLNAME.rpt after synthesis";;
	
	# Extract throughput
	(my $throughput_rpt) = $syn_rpt =~ m/^############### EFFECTIVE THROUGHPUT([^#]+)#/gm;
	for my $mode (qw(2b_2b 4b_4b 8b_8b 8b_2b 8b_4b)) {
		($data{"throughput_$mode"}) = $throughput_rpt =~ m/^Mode $mode:\s+([\d\.]+)/m or die print_error "$FULLNAME no throughput_$mode match";
	}
	print_info "$FULLNAME extracted throughputs ($data{throughput_2b_2b}, $data{throughput_4b_4b}, $data{throughput_8b_2b}, $data{throughput_8b_4b}, $data{throughput_8b_8b})";
	
	# Extract delays
	(my $timing_summary) = $syn_rpt =~ m/^############### TIMING - SUMMARY([^#]+)#/gm;
	for my $mode (qw(2b_2b 4b_4b 8b_8b 8b_2b 8b_4b)) {
		# Get clock
		my $CHOSEN_CLK = $CLK_8B;
		$CHOSEN_CLK = $CLK_2B if ($mode eq "2b_2b");
		$CHOSEN_CLK = $CLK_4B if ($mode eq "4b_4b");
		# Find delay
		$timing_summary =~ m/Timing slack\s+:\s+([-\d]+)ps.*\n.*\n.*\nMode\s+:\s+$mode/m or die print_error "$FULLNAME no delay_$mode match";
		$data{"delay_$mode"} = sprintf("%.3f", $CHOSEN_CLK - ($1/1000));
	}
	print_info "$FULLNAME extracted clocks ($data{delay_2b_2b}, $data{delay_4b_4b}, $data{delay_8b_2b}, $data{delay_8b_4b}, $data{delay_8b_8b})";
	
	# Loop on DVFS delays
	VOLTAGE: for (my $VOLTAGE = 0.800; $VOLTAGE <= 1.000; $VOLTAGE += 0.025) {
		
		# 3 digits
		$VOLTAGE = sprintf("%.3f", $VOLTAGE);
		
		# Extract delays
		(my $timing_summary) = $syn_rpt =~ m/^############### TIMING ${VOLTAGE}V - SUMMARY([^#]+)/gm or die print_error "$FULLNAME no timing summary for voltage $VOLTAGE";
		for my $mode (qw(2b_2b 4b_4b 8b_8b 8b_2b 8b_4b)) {
			# Get clock
			my $CHOSEN_CLK = $CLK_8B;
			$CHOSEN_CLK = $CLK_2B if ($mode eq "2b_2b");
			$CHOSEN_CLK = $CLK_4B if ($mode eq "4b_4b");
			# Find delay
			$timing_summary =~ m/Timing slack\s+:\s+([-\d]+)ps.*\n.*\n.*\nMode\s+:\s+$mode/m or die print_error "$FULLNAME no delay_${mode}_$VOLTAGE match$timing_summary";
			$data{"delay_${mode}_$VOLTAGE"} = sprintf("%.3f", $CHOSEN_CLK - ($1/1000));
		}
	
	}
	
	# Close report file
	undef $syn_rpt;
	
	#################################### Simulations
	
	# Loop VCD
	W_CHOSEN_WIDTH: for my $W_CHOSEN_WIDTH (2,4,8) {
	A_CHOSEN_WIDTH: for my $A_CHOSEN_WIDTH (uniq($W_CHOSEN_WIDTH,8)) {
		
		# Mode
		my $mode  = "${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b";
		
		# Choose delay
		my $CLK_PERIOD = $data{"delay_$mode"};
		
		# Timing margin to avoid Modelsim errors
		$CLK_PERIOD = sprintf("%.3f", $CLK_PERIOD + $TIMING_MARGIN); 
		
		# Prepare simulation script
		my $sim  = sprintf("%s_clk%.3f", $mode, $CLK_PERIOD);
		open sim_pb_fp, ">sim_${sim}_setup.tcl" or die print_error "$FULLNAME failed to write sim_${sim}_setup.tcl";
		print sim_pb_fp <<EOF;
############ DESIGN PARAMETERS ############

# Files
set VERILOG_FILE    $FULLNAME.v
set SDF_FILE        $FULLNAME.sdf
set PB_FILE         $PB_FILE

# Directories
set ASSERT_DIR      $ASSERT_DIR

# Simulation mode
set CLK_PERIOD      $CLK_PERIOD
set A_CHOSEN_WIDTH  $A_CHOSEN_WIDTH
set W_CHOSEN_WIDTH  $W_CHOSEN_WIDTH

# Setup
set STIMULI_MAX     10000
set LIB_V           $LIB_V

set AUTO            yes
EOF
		close sim_pb_fp;
		
		# Run sim
		print_info "$FULLNAME sim ($sim)";
		my $sim_log = ($verbose < 2 ? " >> sim_pb.log" : "");
		my $status = system("eda mgc vsim -batch -do sim_${sim}_setup.tcl -do \"$SIM_PB_FILE $sim_log\"");
		if ($status != 0) { die print_error "$FULLNAME failed sim ($sim)"; }
		
		# Correct VCD file (remove pt_mac_serial scope)
		my $status = system("sed -e '10,11d' -i dump_$sim.vcd");
		if ($status != 0) { die print_error "$FULLNAME failed sed into dump_$sim.vcd"; }
		
		# Prepare power extraction script
		open power_fp, ">power_$sim.tcl" or die print_error "$FULLNAME failed to write power_$sim.tcl";
		print power_fp <<EOF;
################# LIBRARY #################

set_attribute library $LIB_DB

################# DESIGN ##################

set_attribute lp_power_analysis_effort high

read_hdl -library work $FULLNAME.v

elaborate top_$DESIGN

############### ANALYZE VCD ###############

read_vcd -static dump_$sim.vcd

############### REPORT POWER ##############

echo "\\n############### POWER - $mode SUMMARY\\nSimulated at $CLK_PERIOD clock period.\\n" >> $FULLNAME.rpt
report power -verbose >> $FULLNAME.rpt

echo "\\n############### POWER - $mode DETAILS\\nSimulated at $CLK_PERIOD clock period.\\n" >> $FULLNAME.rpt
report power -flat -sort dynamic >> $FULLNAME.rpt

# Clean-up
delete_obj designs/*
EOF
		close power_fp;
		
		# Run syn
		print_info "$FULLNAME power extraction ($sim)";
		my $power_log = ($verbose < 2 ? " >> power.log" : "");
		system "tcsh -c 'genus -legacy_ui -batch -f power_$sim.tcl'$power_log";
		my $status = system "tail -2 power.log | grep -q -P 'Abnormal|problems'";
		if ($status == 0) { die print_error "$FULLNAME failed power extraction ($sim)"; }
		
	}}

	my $status = system "grep -q -P 'Errors: [1-9]' sim_pb.log";
	if ($status == 0) { die print_error "$FULLNAME detected error in power bench log"; }
	
	#################################### Data extraction
	
	# Extract report
	my $syn_rpt = do {
		local $/;
		open syn_rpt_fp, "$FULLNAME.rpt";
		<syn_rpt_fp>
	} or die "ERROR: Failed to read $FULLNAME.rpt";
	
	# Area
	(my $area_rpt) = $syn_rpt =~ m/^############### AREA - SUMMARY([^#]+)#/gm;
	$area_rpt =~ m/^top_mac\S*\s+(\d+)\s+(\d+)\s+\d+\s+(\d+)\s+\S+/gm or die print_error "$FULLNAME no top area match";
	$data{top_cells}         = $1;
	#$data{top_cell_area}     = $2;
	$data{top_total_area}    = $3;
	$area_rpt =~ m/^\s+mac\s+mac\S*\s+(\d+)\s+(\d+)\s+\d+\s+(\d+)\s+\S+/gm or die print_error "$FULLNAME no mac area match";
	$data{mac_cells}         = $1;
	#$data{mac_cell_area}     = $2;
	$data{mac_total_area}    = $3;
	
	# Power summary
	(my $power_rpt) = $syn_rpt =~ m/^############### POWER - SUMMARY([^#]+)#/gm;
	$power_rpt =~ m/^top_mac\S*\s+\d+\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)/gm or die print_error "$FULLNAME no top power match";
	$data{top_leakage_power} = $1;
	$data{top_dynamic_power} = $2;
	$data{top_total_power}   = $3;
	$power_rpt =~ m/^\s+mac\s+\d+\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)/gm or die print_error "$FULLNAME no mac power match";
	$data{mac_leakage_power} = $1;
	$data{mac_dynamic_power} = $2;
	$data{mac_total_power}   = $3;
	
	# Loop VCD
	W_CHOSEN_WIDTH_RPT: for my $W_CHOSEN_WIDTH (2,4,8) {
	A_CHOSEN_WIDTH_RPT: for my $A_CHOSEN_WIDTH (uniq($W_CHOSEN_WIDTH,8)) {
		
		# Mode
		my $mode  = "${A_CHOSEN_WIDTH}b_${W_CHOSEN_WIDTH}b";
		
		# Power from top and mac modules
		(my $power_rpt) = $syn_rpt =~ m/^############### POWER - $mode SUMMARY([^#]+)#/gm;
		$power_rpt =~ m/^top_mac\S*\s+\d+\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)/gm  or die print_error "$FULLNAME no top power match in mode $mode";
		$data{"top_leakage_power_$mode"}  = $1;
		$data{"top_dynamic_power_$mode"}  = $4;
		$data{"top_total_power_$mode"}    = $5;
		$power_rpt =~ m/^\s+mac\s+\d+\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)/gm  or die print_error "$FULLNAME no mac power match in mode $mode";
		$data{"mac_leakage_power_$mode"}  = $1;
		$data{"mac_dynamic_power_$mode"}  = $4;
		$data{"mac_total_power_$mode"}    = $5;
		
		# Power from clock gating networks
		$data{"cg_leakage_power_$mode"}  = 0;
		$data{"cg_dynamic_power_$mode"}  = 0;
		$data{"cg_total_power_$mode"}    = 0;
		while($power_rpt =~ m/\s+\S*_CG_\S*\s+\d+\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)\s+([\d\.]+)/g) {
			$data{"cg_leakage_power_$mode"}  += $1;
			$data{"cg_dynamic_power_$mode"}  += $4;
			$data{"cg_total_power_$mode"}    += $5;
		}
		
	}}
	
	#################################### Data writing
	
	# Write data on report
	open rpt_fp, ">>$FULLNAME.rpt" or die print_error "$FULLNAME failed to append $FULLNAME.rpt";
	print rpt_fp "############### EXTRACTED DATA\n\n";
	print rpt_fp sprintf "%-25s %s\n", "name", "$FULLNAME";
	print rpt_fp sprintf "%-25s %s\n", $_,     $data{$_}  foreach (keys %data);
	print rpt_fp "\n############### RESULT LINE\n\n";
	
	# Open/lock result file
	local $| = 1;
	open my $result_fp, ">>$RESULT_FILE" or die print_error "$FULLNAME failed to append $RESULT_FILE";
	lock($result_fp) or die print_error "$FULLNAME failed to lock $RESULT_FILE";
	
	# First line
	my $line = sprintf "%-70s", "name,";
	$line   .= sprintf "%-*s", max(length($_)+3,13), "$_," foreach (keys %data);
	$line   =~ s/,\s+$/\n/;
	print rpt_fp $line;
	if ($pm_count <= $max_threads) {
		if (-s $RESULT_FILE == 0) {
			print $result_fp $line or die print_error "$FULLNAME failed to write in $RESULT_FILE";
		}
	}
	
	# Data line
	my $line = sprintf "%-70s", "$FULLNAME,";
	$line   .= sprintf "%-*s", max(length($_)+3,13), "$data{$_}," foreach (keys %data);
	$line   =~ s/,\s+$/\n/;
	print $result_fp $line or die print_error "$FULLNAME failed to write in $RESULT_FILE";
	print rpt_fp $line;
	
	# Unlock and close files
	unlock($result_fp) or die print_error "$FULLNAME failed to unlock $RESULT_FILE";
	close $result_fp or die print_error "$FULLNAME failed to close $RESULT_FILE";
	close rpt_fp;
	
	#################################### Clean-up files and tmp directory
	
	# Move files to keep
	my $status = system("mv $FULLNAME.rpt $REPORT_DIR/.");
	if ($status != 0) { die print_error "$FULLNAME.rpt failed moving to $REPORT_DIR"; }
	my $status = system("mv $FULLNAME.v   $EXPORT_DIR/.");
	if ($status != 0) { die print_error "$FULLNAME.v failed moving to $EXPORT_DIR"; }
	my $status = system("mv $FULLNAME.sdf $EXPORT_DIR/."); 
	if ($status != 0) { die print_error "$FULLNAME.sdf failed moving to $EXPORT_DIR"; }
	my $status = system("mv sim_pb.log    $EXPORT_DIR/$FULLNAME.sim.log"); 
	if ($status != 0) { die print_error "$FULLNAME failed moving sim log to $EXPORT_DIR"; }
	my $status = system("mv syn.log       $EXPORT_DIR/$FULLNAME.syn.log"); 
	if ($status != 0) { die print_error "$FULLNAME failed moving syn log to $EXPORT_DIR"; }
	my $status = system("mv power.log     $EXPORT_DIR/$FULLNAME.power.log"); 
	if ($status != 0) { die print_error "$FULLNAME failed moving power log to $EXPORT_DIR"; }
	
	# Delete tmp dir
	my $status = system("rm $TMP_DIR -rf"); 
	if ($status != 0) { die print_error "$FULLNAME failed deleting tmp directory"; }
	
	# Finish
	$pm->finish(0);

}}}}

# Finish children
$pm->wait_all_children;
print_warning "end of script, all children finished";
