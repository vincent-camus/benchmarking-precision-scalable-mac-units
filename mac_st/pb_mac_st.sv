//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    pb_mac_st
// Function:  testbench for gate-level verification and SAIF/SVD power estimation
// Version:   1.0
//-----------------------------------------------------

`timescale 1ns/1ps

module pb_mac_st ();

	//-------------Testbench parameter---------------------
	parameter  W_CHOSEN_WIDTH;
	parameter  A_CHOSEN_WIDTH;
	parameter  VCD_FILE;
	parameter  STIMULI_MAX;
	parameter  CLK_PERIOD;
	parameter  STIMULI_FILE;
	
	//-------------Design parameter------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4;
	parameter  CONFIG_AW_WIDTH = 1;
	
	//-------------Local design parameters-----------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------Local testbench parameters--------------
	localparam W_ACTIVE_WIDTH  = 2**($clog2(W_CHOSEN_WIDTH)) > W_WIDTH/(2**CONFIG_AW_WIDTH)
		? 2**($clog2(W_CHOSEN_WIDTH)) : W_WIDTH/(2**CONFIG_AW_WIDTH);
	localparam A_ACTIVE_WIDTH  = 2**($clog2(A_CHOSEN_WIDTH)) > A_WIDTH/(2**CONFIG_AW_WIDTH)
		? 2**($clog2(A_CHOSEN_WIDTH)) : A_WIDTH/(2**CONFIG_AW_WIDTH);
	localparam AW_ACTIVE_WIDTH = (W_ACTIVE_WIDTH > A_ACTIVE_WIDTH) ? W_ACTIVE_WIDTH : A_ACTIVE_WIDTH;
	localparam PARALLEL_OPS    = W_WIDTH/AW_ACTIVE_WIDTH;
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       rst;
	logic                       accu_rst;
	
	// config
	logic [CONFIG_AW_WIDTH-1:0] config_aw;   // LSB clock-gates LSBs
	
	// operands & output
	logic         [A_WIDTH-1:0] a;           // unsigned
	logic         [W_WIDTH-1:0] w;           // signed
	logic         [Z_WIDTH-1:0] z;           // signed
	
	//-------------Bench signals---------------------------

	// lines
	logic  [W_CHOSEN_WIDTH-1:0] w_line;
	logic  [A_CHOSEN_WIDTH-1:0] a_line;
	
	// operands & output
	logic [AW_ACTIVE_WIDTH-1:0] a_mini [0:PARALLEL_OPS-1];
	logic [AW_ACTIVE_WIDTH-1:0] w_mini [0:PARALLEL_OPS-1];
	
	// files
	integer                     stimuli_fp;
	integer                     stimuli_nb;  // stimuli counter
	integer                     status;      // file reading
	
	//-------------DUT instantiation-----------------------
	top_mac_st top_mac_st (
		// Inputs
		.clk       (clk),
		.rst       (rst),
		.accu_rst  (accu_rst),
		.config_aw (config_aw),
		.w         (w),
		.a         (a),
		// Outputs
		.z         (z)
	);
	
	//-------------Assertion binding-----------------------
	// bind top_mac_st assertion_binding sva (.*);
	
	//-------------Clock-----------------------------------
	initial clk = 0;
	always #(CLK_PERIOD/2) clk = ~clk;
	
	//-------------Bench-----------------------------------
	
	// mini-operand aligner
	generate
		for (genvar block = 0; block < PARALLEL_OPS; block++) begin
			assign w[(block+1)*AW_ACTIVE_WIDTH-1:block*AW_ACTIVE_WIDTH] = w_mini[block];
			assign a[(block+1)*AW_ACTIVE_WIDTH-1:block*AW_ACTIVE_WIDTH] = a_mini[block];
		end
	endgenerate
	
	// bench process
	initial begin
		
		// print
		$display("** Info: starting w%0d_a%0d_%1.3f with %0d stimuli.",
			W_CHOSEN_WIDTH, A_CHOSEN_WIDTH, CLK_PERIOD, STIMULI_MAX);
		
		// open stimuli file
		stimuli_fp = $fopen(STIMULI_FILE, "r");
		stimuli_nb = 0;
		
		// initial rst
		rst       = 1;
		accu_rst  = 1;
		config_aw = 0; // exception for MAC_ST: reset at config 0
		for (int block = 0; block < PARALLEL_OPS; block++) begin
			w_mini[block] = 0;
			a_mini[block] = 0;
		end
		repeat (5) @(negedge clk);
		
		// set precision and continue rst
		config_aw = (W_WIDTH/AW_ACTIVE_WIDTH)-1;
		repeat (4) @(negedge clk);
		
		// VCD dump file
		$dumpfile(VCD_FILE);
		$dumpvars(0, top_mac_st);
		
		// repeat accumulation cycles
		repeat (10000) begin
		
			// accu reset
			rst      = 0;
			accu_rst = 1;
			for (int block = 0; block < PARALLEL_OPS; block++) begin
				w_mini[block] = 0;
				a_mini[block] = 0;
			end
			@(negedge clk);
			
			// repeat operations
			repeat (50) begin
				
				// align mini-operands
				for (int block = 0; block < PARALLEL_OPS; block++) begin
					
					// scan operands from file
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					
					// correct operands
					w_mini[block] = w_line << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_mini[block] = a_line << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
				end
				
				// processing and wait
				rst      = 0;
				accu_rst = 0;
				@(negedge clk);
				
			end
		end
	$stop;
	end // end simulation
	
endmodule // pb_mac_st
