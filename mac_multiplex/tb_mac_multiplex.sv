//-----------------------------------------------------
// Author:	  Vincent Camus
// Design:	  tb_mac_multiplex
// Version:   1.0
// Function:  testbench for multiplex MAC with symmetric configurability
//-----------------------------------------------------


module tb_mac_multiplex ();

	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for each accumulator
	parameter  CONFIG_AW_WIDTH = 2; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+(2**CONFIG_AW_WIDTH)*PLUS_WIDTH;
	localparam CONFIG_SC_WIDTH = 2**(CONFIG_AW_WIDTH+1)-1;
	
	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk;
	logic                       rst;
	logic                       accu_rst;
	
	// config
	logic [CONFIG_AW_WIDTH-1:0] config_aw;   // LSB clock-gates LSBs
	
	// operands
	logic         [W_WIDTH-1:0] w;           // signed
	logic         [A_WIDTH-1:0] a;           // unsigned
	
	// outputs
	logic         [Z_WIDTH-1:0] z;           // signed
	
	//-------------Bench signals---------------------------
	integer                     aw_bits;     // number of bits desired
	
	//-------------Waveform debug signals------------------
	
	// mode 4
	logic [A_WIDTH/4-1:0] a0_mode4,     a1_mode4,     a2_mode4,     a3_mode4;
	logic [W_WIDTH/4-1:0] w0_mode4,     w1_mode4,     w2_mode4,     w3_mode4;
	logic [Z_WIDTH/4-1:0] m0_mode4_exp, m1_mode4_exp, m2_mode4_exp, m3_mode4_exp;
	logic [Z_WIDTH/4-1:0] z0_mode4_exp, z1_mode4_exp, z2_mode4_exp, z3_mode4_exp;
	logic [Z_WIDTH/4-1:0] z0_mode4,     z1_mode4,     z2_mode4,     z3_mode4;
	
	// mode 2
	logic [A_WIDTH/2-1:0] a0_mode2,     a1_mode2;
	logic [W_WIDTH/2-1:0] w0_mode2,     w1_mode2;
	logic [Z_WIDTH/2-1:0] m0_mode2_exp, m1_mode2_exp;
	logic [Z_WIDTH/2-1:0] z0_mode2_exp, z1_mode2_exp;
	logic [Z_WIDTH/2-1:0] z0_mode2,     z1_mode2;
	
	// mode 1
	logic [Z_WIDTH/2-1:0] m_exp;
	logic [Z_WIDTH/2-1:0] z_exp;
	
	//-------------UUT instantiation-----------------------
	top_mac_multiplex #(
		// Parameters
		.W_WIDTH         (W_WIDTH),
		.A_WIDTH         (A_WIDTH),
		.PLUS_WIDTH      (PLUS_WIDTH),
		.CONFIG_AW_WIDTH (CONFIG_AW_WIDTH)
	)
	top_mac (
		// Inputs
		.clk       (clk),
		.rst       (rst),
		.config_aw (config_aw),
		.accu_rst  (accu_rst),
		.w         (w),
		.a         (a),
		// Outputs
		.z         (z)
	);
	
	//-------------Assertion binding-----------------------
	bind top_mac_multiplex assertion_binding #(W_WIDTH, A_WIDTH, PLUS_WIDTH, CONFIG_AW_WIDTH) sva (.*);
	
	//-------------Clock-----------------------------------
	initial clk = 0;
	always #5 clk = ~clk;
	
	//-------------Waveform debug--------------------------
	
	// mode 4
	assign a3_mode4 = a[4*A_WIDTH/4-1:3*A_WIDTH/4];
	assign a2_mode4 = a[3*A_WIDTH/4-1:2*A_WIDTH/4];
	assign a1_mode4 = a[2*A_WIDTH/4-1:1*A_WIDTH/4];
	assign a0_mode4 = a[1*A_WIDTH/4-1:0*A_WIDTH/4];
	
	assign w3_mode4 = w[4*W_WIDTH/4-1:3*W_WIDTH/4];
	assign w2_mode4 = w[3*W_WIDTH/4-1:2*W_WIDTH/4];
	assign w1_mode4 = w[2*W_WIDTH/4-1:1*W_WIDTH/4];
	assign w0_mode4 = w[1*W_WIDTH/4-1:0*W_WIDTH/4];
	
	assign z3_mode4 = z[4*Z_WIDTH/4-1:3*Z_WIDTH/4];
	assign z2_mode4 = z[3*Z_WIDTH/4-1:2*Z_WIDTH/4];
	assign z1_mode4 = z[2*Z_WIDTH/4-1:1*Z_WIDTH/4];
	assign z0_mode4 = z[1*Z_WIDTH/4-1:0*Z_WIDTH/4];
	
	// mode 2
	assign a1_mode2 = a[2*A_WIDTH/2-1:1*A_WIDTH/2];
	assign a0_mode2 = a[1*A_WIDTH/2-1:0*A_WIDTH/2];
	
	assign w1_mode2 = w[2*W_WIDTH/2-1:1*W_WIDTH/2];
	assign w0_mode2 = w[1*W_WIDTH/2-1:0*W_WIDTH/2];
		
	assign z1_mode2 = z[2*Z_WIDTH/2-1:1*Z_WIDTH/2];
	assign z0_mode2 = z[1*Z_WIDTH/2-1:0*Z_WIDTH/2];
	
	// debug expected mult
	always @(posedge clk) begin
		if (rst) begin
			// mode 4
			m3_mode4_exp = 0;
			m2_mode4_exp = 0;
			m1_mode4_exp = 0;
			m0_mode4_exp = 0;
			// mode 2
			m1_mode2_exp = 0;
			m0_mode2_exp = 0;
			// mode 1
			m_exp        = 0;
		end
		else begin
			// mode 4
			m3_mode4_exp = $signed({1'b0, a3_mode4}) * $signed(w3_mode4);
			m2_mode4_exp = $signed({1'b0, a2_mode4}) * $signed(w2_mode4);
			m1_mode4_exp = $signed({1'b0, a1_mode4}) * $signed(w1_mode4);
			m0_mode4_exp = $signed({1'b0, a0_mode4}) * $signed(w0_mode4);
			// mode 2
			m1_mode2_exp = $signed({1'b0, a1_mode2}) * $signed(w1_mode2);
			m0_mode2_exp = $signed({1'b0, a0_mode2}) * $signed(w0_mode2);
			// mode 1
			m_exp        = $signed({1'b0, a})        * $signed(w);
		end
	end
			
	// debug expected accu
	always @(posedge clk) begin
		if (rst || accu_rst) begin
			// mode 4
			z3_mode4_exp = 0;
			z2_mode4_exp = 0;
			z1_mode4_exp = 0;
			z0_mode4_exp = 0;
			// mode 2
			z1_mode2_exp = 0;
			z0_mode2_exp = 0;
			// mode 1
			z_exp        = 0;
		end
		else begin
			// mode 4
			z3_mode4_exp = $signed(z3_mode4_exp) + $signed(m3_mode4_exp);
			z2_mode4_exp = $signed(z2_mode4_exp) + $signed(m2_mode4_exp);
			z1_mode4_exp = $signed(z1_mode4_exp) + $signed(m1_mode4_exp);
			z0_mode4_exp = $signed(z0_mode4_exp) + $signed(m0_mode4_exp);
			// mode 2
			z1_mode2_exp = $signed(z1_mode2_exp) + $signed(m1_mode2_exp);
			z0_mode2_exp = $signed(z0_mode2_exp) + $signed(m0_mode2_exp);
			// mode 1
			z_exp        = $signed(z_exp)        + $signed(m_exp);
		end
	end
	
	//-------------Bench-----------------------------------
	
	// bench process
	initial begin
	
		// different weight bitwidth modes
		for (int j = 0; j <= CONFIG_AW_WIDTH; j++) begin
			
			// initial rst
			rst       = 1;
			accu_rst  = 1;
			config_aw = W_WIDTH-1;
			w         = 0;
			a         = 0;
			aw_bits   = 0;
			repeat (5) @(negedge clk);
		
			// set precision
			aw_bits   = W_WIDTH/(2**j);
			config_aw = (W_WIDTH/aw_bits)-1;
			repeat (4) @(negedge clk);
			
			// repeat accumulation cycles
			repeat (10) begin
			
				// rst
				rst      = 1;
				accu_rst = 1;
				w        = 0;
				a        = 0;
				@(negedge clk);
				rst      = 0;
				@(negedge clk);
				
				// repeat operations
				repeat (10) begin
					a        = $random;
					w        = $random;
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
				repeat (10) begin
					a        = $random;
					w        = $random;
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);
				end
				
			end
		end
		$stop;
	end
	
endmodule // tb_mac_multiplex

