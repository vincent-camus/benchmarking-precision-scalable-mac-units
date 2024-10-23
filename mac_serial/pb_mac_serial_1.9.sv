//-----------------------------------------------------
// Author:    Vincent Camus
// File Name: pb_mac_serial_1.0.sv
// Design:    pb_mac_serial
// Function:  testbench for gate-level verification and SAIF/SVD power estimation
// Version:   1.0
//-----------------------------------------------------

`timescale 1ns/1ps

module pb_mac_serial ();

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
	parameter  N_WIDTH         = 2;
	parameter  CONFIG_W_WIDTH  = 2;
	
	//-------------Local design parameters-----------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------Local testbench parameters--------------
	localparam W_ACTIVE_WIDTH  = 2**($clog2(W_CHOSEN_WIDTH)) > W_WIDTH/(2**CONFIG_W_WIDTH)
		? 2**($clog2(W_CHOSEN_WIDTH)) : W_WIDTH/(2**CONFIG_W_WIDTH);
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       rst;
	
	// secondary clk
	logic                       clk_accu;
	logic                       rst_delayed;
	logic                       trigger_accu;
	
	// config
	logic  [CONFIG_W_WIDTH-1:0] config_w;    // LSB clock-gates LSBs
	
	// MAC FSM
	logic                       fsm_last;
	logic                       fsm_accu;
	
	// operands & output
	logic         [A_WIDTH-1:0] a;           // unsigned
	logic         [W_WIDTH-1:0] w;           // signed
	logic         [N_WIDTH-1:0] w_serial;    // signed bit-serial from LSB to MSB
	logic         [W_WIDTH-1:0] w_shifted;   // due to modelsim error
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
	top_mac_serial top_mac_serial (
		// Inputs
		.clk      (clk),
		.clk_accu (clk_accu),
		.rst      (rst),
		.config_w (config_w),
		.fsm_last (fsm_last),
		.fsm_accu (fsm_accu),
		.w_serial (w_serial),
		.a        (a),
		// Outputs
		.z        (z)
	);
	
	//-------------Clock-----------------------------------
	initial clk = 0;
	always #(CLK_PERIOD/2) clk = ~clk;
	
	//-------------Secondary clock-------------------------	
	initial rst_delayed = 0;
	always rst_delayed = #(CLK_PERIOD/2) rst;
	
	always_comb begin
		if (rst) begin
			clk_accu <= clk;
		end
		else begin
			clk_accu <= (rst_delayed | trigger_accu) & clk;
		end
	end
	
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
		config_w  = 0;
		w         = 0;
		a         = 0;
		w_serial  = 0;
		w_shifted = 0;
		fsm_last  = 0;
		fsm_accu  = 1;
		trigger_accu = 0;
		repeat (5) @(negedge clk);
		
		// set precision and continue rst
		config_w = (W_WIDTH/W_CHOSEN_WIDTH)-1;
		repeat (4) @(negedge clk);
		
		// VCD dump file
		$dumpfile(VCD_FILE);
		$dumpvars(0, top_mac_serial);
		
		// repeat accumulation cycles
		repeat (10000) begin
		
			// mini rst with chosen configuration
			rst      = 1;
			w        = 0;
			a        = 0;
			fsm_accu = 0;
			fsm_last = 0;
			@(negedge clk);
			
			// repeat operations
			repeat (50) begin
			
				// operands from file
				status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
				if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
				stimuli_nb++;
				
				// correct operands for data gating
				w = w_line << W_WIDTH-W_CHOSEN_WIDTH; // zero-padded LSBs
				a = a_line << A_WIDTH-A_CHOSEN_WIDTH; // zero-padded LSBs
				
				// shifted w (to avoid modelsim error)
				w_shifted = w >> W_WIDTH-W_ACTIVE_WIDTH;
				
				// apply w bit-serially
				for (int i = 0; i <= (W_ACTIVE_WIDTH/N_WIDTH)-1; i++) begin
					rst      = 0;
					fsm_accu = 0;
					fsm_last = 0;
					trigger_accu = 0;
					w_serial = w_shifted[N_WIDTH-1:0];
					if (i == (W_ACTIVE_WIDTH/N_WIDTH)-1) fsm_last = 1;
					if (i == 0)                          fsm_accu = 1;
					if ((i == 1) || (W_ACTIVE_WIDTH/N_WIDTH == 1)) trigger_accu = 1;
					@(negedge clk);
					w_shifted = w_shifted >> N_WIDTH;
				end
			end
		end
	$stop;
	end // end simulation
	
	//-------------Assert accumulation---------------------
	
	property accumulation;
		// signal declaration
		integer w_sav, a_sav;
		logic [(A_WIDTH+W_WIDTH)+PLUS_WIDTH-1:0] mult_exp, z_val, z_old, z_exp;
		// step 1: get inputs given at posedge
		(!rst & fsm_last,
			mult_exp = $signed({1'b0, a})*$signed(w_line),
			a_sav    = $signed({1'b0, a}),
			w_sav    = $signed(w_line)
		)
		// step 1bis: input stage processing
		|=> @(posedge clk) (!rst)
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst,
			// previous arithmetic z
			z_old = $signed(z) >>> (W_WIDTH-W_CHOSEN_WIDTH),
			// expected arithmetic z
			z_val = $signed(z_old) + $signed(mult_exp),
			// expected binary pattern of z
			z_exp = z_val << (W_WIDTH-W_CHOSEN_WIDTH),
			// print
			$display("------------------------------------------------------------------"),
			$display("Old value:  %b -> %b (%7d)", z, z_old, $signed(z_old) ),
			$display("New arith:  %7d x %7d = %b (%7d)", $signed(w_sav), $signed(a_sav), mult_exp, $signed(mult_exp) ),
			$display("Exp value:  %b <- %b (%7d)", z_exp, z_val, $signed(z_val) )
		)
		// step 2bis: output stage processing
		|=> @(posedge clk) (!rst)
		// step 3: get established outputs and assert
		|=> @(negedge clk) (1'b1,
			// print
			$display("Observed:   %b", z)
		)
		|-> (z_exp == z)
	endproperty // accumulation
	always @(posedge clk) assert property (accumulation);
	
	//-------------Assert reset----------------------------
	
	property reset;
		// step 1: check established inputs at posedge
		(rst,
			// print
			$display("------------------------------------------------------------------"),
			$display("Reset signal")
		)
		// step 1bis: input processing
		|=> @(posedge clk) (1'b1)
		// step 2: check established ouput at negedge
		|-> @(negedge clk) (z == 0)
	endproperty // reset
	always @(posedge clk) assert property (reset);
	
endmodule // pb_mac_serial
