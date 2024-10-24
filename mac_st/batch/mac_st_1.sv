//-------------------------------------------------------------
// Design:        ST MAC unit top with input register & 1-level scalability
// Description:   Sum-Together MAC unit
// Version:       1.0
// Working mode:  8/4-bit

// config_aw = 1'b0 -> 8x8
// config_aw = 1'b1 -> 4x4 + 4x4

// Author:	      Linyan Mei
//-------------------------------------------------------------


module top_mac_st (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------
	//----basic in--------
	input 		             clk;
	input 		             rst;
	input 		             accu_rst;

	//----Data in--------
	input    [7:0]           a ;           // unsigned activation
	input    [7:0]           w ;           // signed / unsigned weight

	//----Control in-----
	input                    config_aw;

	//-------------Outputs---------------------------------
	output   [15+HEADROOM:0] z;

	//-------------Internal signals-----------------------
	reg		 [7:0]           a_reg;
	reg		 [7:0]           w_reg;

	reg                      rst_reg;
	reg                      accu_rst_reg;

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	mac_st #(
		// Parameters
		.HEADROOM   (HEADROOM)
	)
	mac (
		// Inputs
		.clk        (clk),
		.rst        (rst_reg),
		.accu_rst   (accu_rst_reg),
		.a          (a_reg),
		.w          (w_reg),
		.config_aw  ({1'b0,config_aw}),
		// Outputs
		.z          (z)
	);


	// synchronous resets
	always_ff @(posedge clk) begin
		rst_reg       <= rst;
		accu_rst_reg  <= accu_rst;
	end
	
	// input registers
	always_ff @(posedge clk) begin
		if (rst == 1) begin
			w_reg <= 0;
			a_reg <= 0;
		end
		else begin
			w_reg <= w;
			a_reg <= a;
		end
	end

endmodule // top_mac_st


