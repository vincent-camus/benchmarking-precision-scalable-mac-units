//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    top_mac_multiplex
// Version:   1.0
// Function:  input registers, LUT config overhead
// Notes:     synchronous reset, new naming convention
//-----------------------------------------------------


module top_mac_multiplex (clk, rst, accu_rst, config_aw, w, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for each accumulator
	parameter  CONFIG_AW_WIDTH = 1; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+(2**CONFIG_AW_WIDTH)*PLUS_WIDTH;
	localparam M_WIDTH         = A_WIDTH+W_WIDTH;          // bitwidth of the multiplier
	localparam BLOCK_NB        = 2**CONFIG_AW_WIDTH;       // number of partial products
	localparam PS_LEVEL_NB     = CONFIG_AW_WIDTH+1;        // number of levels of partial sums
	localparam BLOCK_WIDTH     = W_WIDTH/BLOCK_NB;         // bitwidth of mini unsigned a operands
	localparam BLOCK_LEVEL_NB  = $clog2(BLOCK_WIDTH);      // addition levels inside mini partial sum tree
	localparam CONFIG_SC_WIDTH = 2**(CONFIG_AW_WIDTH+1)-1; // 1-bit signal per clock-gated block
	
	//-------------Inputs----------------------------------
	
	// general
	input                        clk;
	input                        rst;
	reg                          rst_reg;
	input                        accu_rst;
	reg                          accu_rst_reg;
	
	// precision config
	input  [CONFIG_AW_WIDTH-1:0] config_aw; // LSB clock-gates LSBs
	
	// operands
	input          [W_WIDTH-1:0] w; // signed configurable bitwidth
	reg            [W_WIDTH-1:0] w_reg;
	input          [A_WIDTH-1:0] a; // unsigned configurable bitwidth
	reg            [A_WIDTH-1:0] a_reg;
	
	//-------------Outputs---------------------------------
	output         [Z_WIDTH-1:0] z;
	
	//-------------Internal signals------------------------
	logic  [CONFIG_SC_WIDTH-1:0] config_sc;
	
	//-------------Datapath--------------------------------
	
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

	// MAC module
	mac_multiplex #(
		// Parameters
		.W_WIDTH         (W_WIDTH),
		.A_WIDTH         (A_WIDTH),
		.PLUS_WIDTH      (PLUS_WIDTH),
		.CONFIG_AW_WIDTH (CONFIG_AW_WIDTH)
	)
	mac (
		// Inputs
		.clk       (clk),
		.rst       (rst_reg),
		.config_aw (config_aw),
		.config_sc (config_sc),
		.accu_rst  (accu_rst_reg),
		.w         (w_reg),
		.a         (a_reg),
		// Outputs
		.z         (z)
	);
	
	// external configuration overhead
	generator_sc #(
		// Parameters
		.CONFIG_AW_WIDTH (CONFIG_AW_WIDTH)
	)
	generator_sc (
		// Inputs
		.config_aw (config_aw),
		// Outputs
		.config_sc (config_sc)
	);
	
endmodule // top_mac_multiplex



module generator_sc (config_aw, config_sc);
	
	// parameters
	parameter  CONFIG_AW_WIDTH = 1;
	
	// local parameters
	localparam CONFIG_SC_WIDTH = 2**(CONFIG_AW_WIDTH+1)-1;
	
	// inputs/outputs
	input  [CONFIG_AW_WIDTH-1:0] config_aw;
	output [CONFIG_SC_WIDTH-1:0] config_sc;
	
	// internal signals
	logic [CONFIG_AW_WIDTH:0] config_aw_mode; 
	logic [CONFIG_AW_WIDTH:0] config_sc_mode [CONFIG_SC_WIDTH-1:0];
	
	// datapath
	assign config_aw_mode = (2**CONFIG_AW_WIDTH)/(config_aw+1);
	generate
		for (genvar mode=0; mode<CONFIG_SC_WIDTH; mode++) begin : gen_sc
			assign config_sc_mode[mode]   = mode+1;
			assign config_sc[mode] = |(config_sc_mode[mode] & config_aw_mode);
		end
	endgenerate
	
endmodule // generator_sc