//-----------------------------------------------------
// Author:	  Vincent Camus
// File Name: assertion_binding_1.sv
// Design:	  assertion_binding
// Function:  assert multiplex MAC for 1-bit config width 
//-----------------------------------------------------


module assertion_binding (clk, rst, accu_rst, config_aw, w, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4;
	parameter  CONFIG_AW_WIDTH = 1;
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+(2**CONFIG_AW_WIDTH)*PLUS_WIDTH;
	
	//-------------Inputs----------------------------------
	
	input                        clk;
	input                        rst;
	input                        accu_rst;
	input  [CONFIG_AW_WIDTH-1:0] config_aw;
	input          [W_WIDTH-1:0] w;
	input          [A_WIDTH-1:0] a;
	input          [Z_WIDTH-1:0] z;
	
	//-------------Assert reset----------------------------

	property accumulation_reset;
		// step 1: check established inputs at posedge
		(rst || accu_rst,
			// print
			$display("-----------------------------------------------------------------------------------------------------------------------------"), 
			$display("Reset signal")
		)
		// step 2: wait processing
		|=> @(posedge clk) (1'b1)
		// step 3: check established ouput at negedge
		|-> @(negedge clk) (z == 0)
	endproperty // accumulation_reset
	always @(posedge clk) assert property (accumulation_reset);
	
	//-------------Assert mode 1---------------------------
	
	property accumulation_mode1;
		logic [(A_WIDTH+W_WIDTH)+PLUS_WIDTH-1:0] m_exp;
		logic [(A_WIDTH+W_WIDTH)+PLUS_WIDTH-1:0] z_val;
		logic [(A_WIDTH+W_WIDTH)+PLUS_WIDTH-1:0] z_old;
		logic [Z_WIDTH-1:0]                      z_exp;
		// step 1: check established inputs at posedge
		(!rst && config_aw == 0,
			// mult expected
			m_exp = $signed({1'b0, a})*$signed(w)
		)
		// input processing
		|=> @(posedge clk) (!rst && !accu_rst && (config_aw == 0))
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst && !accu_rst && (config_aw == 0),
			// previous arithmetic z
			z_old = {z[2*Z_WIDTH/2-1           :1*Z_WIDTH/2],
				     z[1*Z_WIDTH/2-1-PLUS_WIDTH:0*Z_WIDTH/2]},
			// expected arithmetic z
			z_val = $signed(m_exp)+$signed(z_old),
			// expected binary pattern of z
			z_exp = {z_val[2*(A_WIDTH+W_WIDTH)/2+PLUS_WIDTH-1:1*(A_WIDTH+W_WIDTH)/2],
					{PLUS_WIDTH{1'b0}}, z_val[1*(A_WIDTH+W_WIDTH)/2-1:0*(A_WIDTH+W_WIDTH)/2] },
			// print
			$display("-----------------------------------------------------------------------------------------------------------------------------"), 
			$display("Old value:  %b -> %b (%7d)",       z, z_old, $signed(z_old) ),
			$display("New arith:  %7d x %7d = %b (%7d)", $signed(w), $signed({1'b0, a}), m_exp, $signed(m_exp) ),
			$display("Exp value:  %b <- %b (%7d)",       z_exp, z_val, $signed(z_val) )
		)
		// step 2bis: check non reset
		|=> @(posedge clk) (!rst && !accu_rst && (config_aw == 0))
		// step 3: check established ouput at negedge
		|=> @(negedge clk) (1'b1, 
			// print
			$display("Observed:   %b", z)
		)
		|-> (z_exp == z)
	endproperty // accumulation_config1_mode1
	always @(posedge clk) assert property (accumulation_mode1);
	
	//-------------Assert mode 2---------------------------
	
	property accumulation_mode2;
		logic [A_WIDTH/2  :0]                      a0, a1;
		logic [W_WIDTH/2-1:0]                      w0, w1;
		logic [(A_WIDTH+W_WIDTH)/2+PLUS_WIDTH-1:0] m0_exp, m1_exp;
		logic [(A_WIDTH+W_WIDTH)/2+PLUS_WIDTH-1:0] z0_val, z1_val;
		logic [(A_WIDTH+W_WIDTH)/2+PLUS_WIDTH-1:0] z0_old, z1_old;
		logic [Z_WIDTH/2-1:0]                      z0_exp, z1_exp;
		// step 1: check established inputs at posedge
		(!rst && config_aw == 1,
			// unsigned a
			a1 = {1'b0, a[2*A_WIDTH/2-1:1*A_WIDTH/2]},
			a0 = {1'b0, a[1*A_WIDTH/2-1:0*A_WIDTH/2]},
			// signed w
			w1 = w[2*W_WIDTH/2-1:1*W_WIDTH/2],
			w0 = w[1*W_WIDTH/2-1:0*W_WIDTH/2],
			// mult expected
			m1_exp = $signed(a1)*$signed(w1),
			m0_exp = $signed(a0)*$signed(w0)
		)
		// input processing
		|=> @(posedge clk) (!rst && !accu_rst && (config_aw == 1))
		// step 2: check previous accumulator value at negedge
		|=> @(negedge clk) (!rst && !accu_rst && (config_aw == 1),
			// previous arithmetic z
			z1_old = {z[2*Z_WIDTH/2-1:1*Z_WIDTH/2]},
			z0_old = {z[1*Z_WIDTH/2-1:0*Z_WIDTH/2]},
			// expected arithmetic z
			z1_exp = $signed(m1_exp)+$signed(z1_old),
			z0_exp = $signed(m0_exp)+$signed(z0_old),
			// print
			$display("-----------------------------------------------------------------------------------------------------------------------------"), 
			$display("Old value:  %b -> %b (%4d)  |  %b -> %b (%4d)", 
				z[2*Z_WIDTH/2-1:1*Z_WIDTH/2], z1_old, $signed(z1_old), 
				z[1*Z_WIDTH/2-1:0*Z_WIDTH/2], z0_old, $signed(z0_old) ),
			$display("New arith:  %4d x %4d = %b (%4d)        |  %4d x %4d = %b (%4d)", 
				$signed(w1), $signed(a1), m1_exp, $signed(m1_exp), 
				$signed(w0), $signed(a0), m0_exp, $signed(m0_exp) ),
			$display("Exp value:  %b <- %b (%4d)  |  %b <- %b (%4d)", 
				z1_exp, z1_exp, $signed(z1_exp), 
				z0_exp, z0_exp, $signed(z0_exp) )
		)
		// step 2bis
		|=> @(posedge clk) (!rst && !accu_rst && (config_aw == 1))
		// step 3: check established ouput at negedge
		|=> @(negedge clk) (1'b1, 
			// print
			$display("Observed:   %b                         |  %b", 
				z[2*Z_WIDTH/2-1:1*Z_WIDTH/2],
				z[1*Z_WIDTH/2-1:0*Z_WIDTH/2] )
		)
		|-> (z1_exp == z[2*Z_WIDTH/2-1:1*Z_WIDTH/2] &&
			 z0_exp == z[1*Z_WIDTH/2-1:0*Z_WIDTH/2]
		)
	endproperty // accumulation_mode2
	always @(posedge clk) assert property (accumulation_mode2);
	
	//-------------Assert mode 4---------------------------
	
	property accumulation_mode4;
		disable iff (1) null
	endproperty // accumulation_mode4
	always @(posedge clk) assert property (accumulation_mode4);
	
endmodule