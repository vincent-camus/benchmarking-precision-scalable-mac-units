//-----------------------------------------------------
// Author:    Vincent Camus
// File Name: tb_mac_serial_1.9.sv
// Design:    tb_mac_serial
// Function:  testbench for mac_serial with weight configurability
// Notes:     secondary accu clk but kept fsm_accu
// Version:   1.9
//-----------------------------------------------------


module tb_mac_serial ();

	//-------------Parameters------------------------------
	parameter W_WIDTH         = 8;
	parameter A_WIDTH         = 8;
	parameter PLUS_WIDTH      = 4; // extra for the MAC accumulator
	parameter N_WIDTH         = 1;
	parameter CONFIG_W_WIDTH  = 2; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH        = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       clk_accu;
	logic                       rst;
	logic                       rst_delayed;
	
	// clock divider
	//logic                 [3:0] counter;
	logic                       trigger_accu;

	// config
	logic  [CONFIG_W_WIDTH-1:0] config_w;    // LSB clock-gates LSBs
	
	// MAC FSM
	logic                       fsm_last;
	logic                       fsm_accu;
	
	// operands
	logic         [W_WIDTH-1:0] w;
	logic         [A_WIDTH-1:0] a;           // unsigned
	logic         [N_WIDTH-1:0] w_serial;    // signed bit-serial from LSB to MSB
	logic         [W_WIDTH-1:0] w_shifted;   // due to modelsim error
	
	// outputs
	logic         [Z_WIDTH-1:0] z;           // signed
	
	//-------------Bench signals---------------------------
	integer                     mult_exp;
	integer                     z_exp;
	integer                     z_shifted;
	integer                     w_bits;      // number of bits desired
	
	//-------------UUT instantiation-----------------------
	top_mac_serial #(
		// Parameters
		.W_WIDTH        (W_WIDTH),
		.A_WIDTH        (A_WIDTH),
		.PLUS_WIDTH     (PLUS_WIDTH),
		.N_WIDTH        (N_WIDTH),
		.CONFIG_W_WIDTH (CONFIG_W_WIDTH)
	)
	UUT (
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
	always #5 clk = ~clk;
	
	//-------------Secondary clock-------------------------	
	initial rst_delayed = 0;
	always rst_delayed = #5 rst;
	
	always_comb begin
		if (rst) begin
			clk_accu <= clk;
		end
		else begin
			clk_accu <= (rst | trigger_accu) & clk & ~rst_delayed;
		end
	end
	
	//-------------Bench-----------------------------------
	
	// expected
	always @(posedge clk) begin
		if (rst) begin
			mult_exp <= 0;
			z_exp    <= 0;
		end
		else begin
			mult_exp <= $signed(w)*$signed({1'b0, a});
			z_exp <= (fsm_accu) ? $signed(z_exp)+($signed(w)*$signed({1'b0, a}) << (W_WIDTH-w_bits)) : $signed(z_exp);
		end
	end

	// expected when lower bitwidth used	
	assign z_shifted = z_exp << W_WIDTH-w_bits;
	
	// bench process
	initial begin
		
		// different weight bitwidth modes
		for (int j = 0; j <= CONFIG_W_WIDTH; j++) begin
			
			// initial rst
			rst       = 1;
			config_w  = 0;
			w         = 0;
			a         = 0;
			w_serial  = 0;
			fsm_last  = 0;
			fsm_accu  = 1;
			w_bits    = 0;
			w_shifted = 0;
			trigger_accu = 0;
			repeat (5) @(negedge clk);
		
			// set precision
			w_bits   = W_WIDTH/(2**j);
			config_w = (W_WIDTH/w_bits)-1;
			repeat (4) @(negedge clk);
			
			// repeat accumulation cycles
			repeat (10) begin
			
				// mini rst with chosen configuration
				rst      = 1;
				w        = 0;
				a        = 0;
				fsm_accu = 0;
				fsm_last = 0;
				@(negedge clk);
				//rst      = 1; // added
				
				// repeat operations
				repeat (50) begin
				
					// random operands
					a = $random;
					w = $random;
					// limit w to the chosen bitwidth
					for (int i = 0; i <= W_WIDTH-1; i++) begin
						if (i > w_bits-1) w[i] = w[w_bits-1];
					end
					w_shifted = w;
					// apply operand bit-serially
					for (int i = 0; i <= (w_bits/N_WIDTH)-1; i++) begin
						rst      = 0;
						fsm_accu = 0;
						fsm_last = 0;
						trigger_accu = 0;
						w_serial[N_WIDTH-1:0] = w_shifted[N_WIDTH-1:0];
						if (i == (w_bits/N_WIDTH)-1) fsm_last = 1;
						if (i == 0)                  fsm_accu = 1;
						if ((i == 1) || (w_bits/N_WIDTH == 1)) trigger_accu = 1;
						@(negedge clk);
						w_shifted = w_shifted >> N_WIDTH;
						//rst      = 0; //changed
					end
				end
			end
		end
		$stop;
	end
	
	//-------------Assert accumulation---------------------
	
	property accumulation;
		// signal declaration
		integer w_sav, a_sav;
		logic [(A_WIDTH+W_WIDTH)+PLUS_WIDTH-1:0] mult_exp, z_val, z_old, z_exp;
		// step 1: get inputs given at posedge
		(!rst & fsm_last,
			mult_exp = $signed({1'b0, a})*$signed(w),
			a_sav    = $signed({1'b0, a}),
			w_sav    = $signed(w)
		)
		// step 1bis: input stage processing
		|=> @(posedge clk) (!rst)
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst,
			// previous arithmetic z
			z_old = $signed(z) >>> (W_WIDTH-w_bits),
			// expected arithmetic z
			z_val = $signed(z_old) + $signed(mult_exp),
			// expected binary pattern of z
			z_exp = z_val << (W_WIDTH-w_bits),
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
			$display("Observed:   %b (%7d)", z, $signed(z_val))
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
	
endmodule // tb_mac_serial
