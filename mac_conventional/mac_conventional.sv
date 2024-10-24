//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    mac_conventional
// Version    1.0
// Function:  conventional MAC with symmetric configurability
//-----------------------------------------------------


module mac_conventional (clk, rst, accu_rst, w, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for the MAC accumulator
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------Inputs----------------------------------
	
	// basic
	input                        clk;
	input                        rst;
	input                        accu_rst;
	
	// operands
	input          [W_WIDTH-1:0] w; // signed configurable bitwidth
	input          [A_WIDTH-1:0] a; // unsigned configurable bitwidth
	
	//-------------Outputs---------------------------------
	output reg     [Z_WIDTH-1:0] z;
	logic          [Z_WIDTH-1:0] z_tmp;
	
	//-------------Internal signals------------------------
	reg    [A_WIDTH+W_WIDTH-1:0] mult;
	logic  [A_WIDTH+W_WIDTH-1:0] mult_tmp;
	
	//-------------Datapath--------------------------------
	
	// multiplication flip-flops
	always_ff @(posedge clk) begin
		if (rst == 1)
			mult <= 0;
		else
			mult <= mult_tmp;
	end
	//assign mult = mult_tmp; // non-pipelined mode
	
	// accumulation flip-flops
	always_ff @(posedge clk) begin
		if (rst == 1 || accu_rst == 1)
			z <= 0;
		else
			z <= z_tmp;
	end
	
	// signed multiplication
	assign mult_tmp = $signed(w) * $signed({1'b0, a});
	
	// accumulator
	assign z_tmp = $signed(z) + $signed(mult);
	
endmodule // mac_conventional
