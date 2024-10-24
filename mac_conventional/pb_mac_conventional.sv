//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    pb_mac_conventional
// Function:  testbench for gate-level verification and SAIF/SVD power estimation
// Version:   1.0
//-----------------------------------------------------

`timescale 1ns/1ps

module pb_mac_conventional ();
	
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
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       rst;
	logic                       accu_rst;
	
	// operands & output
	logic         [A_WIDTH-1:0] a;           // unsigned
	logic         [W_WIDTH-1:0] w;           // signed
	logic         [Z_WIDTH-1:0] z;           // signed
	
	//-------------Bench signals---------------------------

	// lines
	logic  [W_CHOSEN_WIDTH-1:0] w_line;
	logic  [A_CHOSEN_WIDTH-1:0] a_line;
	
	// files
	integer                     stimuli_fp;
	integer                     stimuli_nb;  // stimuli counter
	integer                     status;      // file reading
	
	//-------------DUT instantiation-----------------------
	top_mac_conventional top_mac_conventional (
		// Inputs
		.clk       (clk),
		.rst       (rst),
		.accu_rst  (accu_rst),
		.w         (w),
		.a         (a),
		// Outputs
		.z         (z)
	);
	
	//-------------Clock-----------------------------------
	initial clk = 0;
	always #(CLK_PERIOD/2) clk = ~clk;
	
	//-------------Bench-----------------------------------
	
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
		w         = 0;
		a         = 0;
		repeat (5) @(negedge clk);
		
		// set precision and continue rst
		repeat (4) @(negedge clk);
		
		// VCD dump file
		$dumpfile(VCD_FILE);
		$dumpvars(0, top_mac_conventional);
		
		// repeat accumulation cycles
		repeat (10000) begin
			
			// accu reset
			rst      = 0;
			accu_rst = 1;
			w        = 0;
			a        = 0;
			@(negedge clk);
			
			// repeat operations
			repeat (50) begin
				
				// scan operands from file
				status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
				if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
				stimuli_nb++;
				
				// correct operands
				w = w_line << W_WIDTH-W_CHOSEN_WIDTH;
				a = a_line << A_WIDTH-A_CHOSEN_WIDTH;
				rst      = 0;
				accu_rst = 0;
				@(negedge clk);
				
			end
		end
		
	$stop;
	end // end simulation
	
	//-------------Assert reset----------------------------
	
	property reset;
		// step 1: check established inputs at posedge
		(rst || accu_rst,
			// print
			$display("---------------------------------------------"), 
			$display("Reset signal")
		)
		// step 2: wait processing
		|=> @(posedge clk) (1'b1)
		// step 3: check established ouput at negedge
		|-> @(negedge clk) (z == 0)
	endproperty // reset
	always @(posedge clk) assert property (reset);
	
	//-------------Assert accumulation---------------------
	
	property accumulation;
		logic [A_WIDTH+W_WIDTH+PLUS_WIDTH-1:0] m_exp, z_old;
		logic [Z_WIDTH-1:0]                    z_exp;
		integer                                a_val, w_val;
		// step 1: check established inputs at posedge
		(!rst,
			// mult expected
			m_exp = $signed(w) * $signed({1'b0, a}),
			a_val = $signed({1'b0, a}),
			w_val = $signed(w)
		)
		// input processing
		|=> @(posedge clk) (!rst && !accu_rst)
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst && !accu_rst,
			// previous arithmetic z
			z_old = z,
			// expected arithmetic z
			z_exp = $signed(m_exp) + $signed(z_old),
			// print
			$display("---------------------------------------------"), 
			$display("Old value:  %b (%7d)", z_old, $signed(z_old) ),
			$display("New arith:  %7d x %7d = %b (%7d)", w_val, a_val, m_exp, $signed(m_exp) ),
			$display("Exp value:  %b (%7d)", z_exp, $signed(z_exp) )
		)
		// step 2bis: check non reset
		|=> @(posedge clk) (!rst && !accu_rst)
		// step 3: check established ouput at negedge
		|=> @(negedge clk) (1'b1, 
			// print
			$display("Observed:   %b", z)
		)
		|-> (z_exp == z)
	endproperty // accumulation
	always @(posedge clk) assert property (accumulation);
	
endmodule // pb_mac_conventional
