//-----------------------------------------------------
// Author:    Vincent Camus
// File Name: top_mac_conventional.sv
// Design:    top_mac_conventional
// Function:  input registers
// Notes:     synchronous reset, new naming convention
//-----------------------------------------------------


module top_mac_conventional (clk, rst, accu_rst, w, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for the MAC accumulator
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------Inputs----------------------------------
	
	// general
	input                        clk;
	input                        rst;
	reg                          rst_reg;
	input                        accu_rst;
	reg                          accu_rst_reg;
	
	// operands
	input          [W_WIDTH-1:0] w; // signed configurable bitwidth
	reg            [W_WIDTH-1:0] w_reg;
	input          [A_WIDTH-1:0] a; // unsigned configurable bitwidth
	reg            [A_WIDTH-1:0] a_reg;
	
	//-------------Outputs---------------------------------
	output         [Z_WIDTH-1:0] z;
	
	//-------------Datapath--------------------------------
	
	// synchronous resets
	always_ff @(posedge clk) begin
		rst_reg      <= rst;
		accu_rst_reg <= accu_rst;
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

	// MAC module
	mac_conventional #(
		// Parameters
		.W_WIDTH    (W_WIDTH),
		.A_WIDTH    (A_WIDTH),
		.PLUS_WIDTH (PLUS_WIDTH)
	)
	mac (
		// Inputs
		.clk      (clk),
		.rst      (rst_reg),
		.accu_rst (accu_rst_reg),
		.w        (w_reg),
		.a        (a_reg),
		// Outputs
		.z        (z)
	);
	
endmodule // top_mac_conventional
