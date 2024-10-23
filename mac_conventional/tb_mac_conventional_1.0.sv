//-----------------------------------------------------
// Author:	  Vincent Camus
// File Name: tb_mac_conventional_1.0.sv
// Design:	  tb_mac_conventional
// Function:  testbench for conventional MAC with symmetric configurability
//-----------------------------------------------------


module tb_mac_conventional ();
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH        = 8;
	parameter  A_WIDTH        = 8;
	parameter  PLUS_WIDTH     = 4; // extra for the MAC accumulator
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH        = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       rst;
	logic                       accu_rst;
	
	// operands
	logic         [W_WIDTH-1:0] w;           // signed
	logic         [A_WIDTH-1:0] a;           // unsigned
	
	//-------------Outputs---------------------------------
	logic         [Z_WIDTH-1:0] z;           // signed
	
	//-------------Waveform debug signals------------------
	integer                     mult_exp;
	integer                     z_exp;
	
	//-------------Bench signals---------------------------
	integer                     w_bits; // number of bits desired
	integer                     a_bits; // number of bits desired
	
	//-------------UUT instantiation-----------------------
	top_mac_conventional #(
		// Parameters
		.W_WIDTH        (W_WIDTH),
		.A_WIDTH        (A_WIDTH),
		.PLUS_WIDTH     (PLUS_WIDTH)
	)
	top_mac (
		// Inputs
		.clk      (clk),
		.rst      (rst),
		.accu_rst (accu_rst),
		.w        (w),
		.a        (a),
		// Outputs
		.z        (z)
	);
	
	//-------------Clock-----------------------------------
	initial clk = 0;
	always #5 clk = ~clk;
	
	//-------------Waveform debug--------------------------
	
	// expected
	always @(posedge clk) begin
		if (rst) begin
			mult_exp <= 0;
			z_exp    <= 0;
		end
		else begin
			mult_exp <= $signed(w) * $signed({1'b0, a});
			z_exp    <= $signed(z_exp) + $signed(mult_exp);
		end
	end
	
	//-------------Bench-----------------------------------
	
	// bench process
	initial begin
	
		// different bitwidth modes
		for (int i = 0; i <= 2; i++) begin
			for (int j = 0; j <= 2; j++) begin
				
				// initial rst
				rst       = 1;
				accu_rst  = 1;
				w         = 0;
				a         = 0;
				w_bits    = 0;
				a_bits    = 0;
				repeat (5) @(negedge clk);
			
				// set precision
				w_bits    = W_WIDTH/(2**i);
				a_bits    = A_WIDTH/(2**j);
				repeat (4) @(negedge clk);
				
				// repeat accumulation cycles
				repeat (2) begin
				
					// rst
					rst      = 1;
					accu_rst = 1;
					w        = 0;
					a        = 0;
					@(negedge clk);
					rst      = 0;
					@(negedge clk);
					
					// repeat operations
					repeat (300) begin
						a        = $random << (A_WIDTH-a_bits);
						w        = $random << (W_WIDTH-w_bits);
						rst      = 0;
						accu_rst = 0;
						@(negedge clk);
					end

					// accu_rst
					accu_rst = 1;
					w        = 0;
					a        = 0;
					@(negedge clk);
					
					// repeat operations
					repeat (300) begin
						a        = $random << (A_WIDTH-a_bits);
						w        = $random << (W_WIDTH-w_bits);
						rst      = 0;
						accu_rst = 0;
						@(negedge clk);
					end
					
				end
			end
		end
		$stop;
	end
	
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
	
	//-------------Assert overflow-------------------------
	
	property overflow;
		integer m_exp, z_exp;
		// step 1: check established inputs at posedge
		(!rst,
			// mult expected
			m_exp = $signed(w) * $signed({1'b0, a})
		)
		// input processing
		|=> @(posedge clk) (!rst && !accu_rst)
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst && !accu_rst,
			// expected arithmetic z
			z_exp = $signed(m_exp) + $signed(z)
		)
		// step 2bis: check non reset
		|=> @(posedge clk) (!rst && !accu_rst)
		// step 3: check established ouput at negedge
		|=> (z_exp == $signed(z))
	endproperty // overflow
	always @(posedge clk) assert property (overflow);
	
endmodule // tb_mac_conventional
