//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    mac_multiplex
// Version:   1.1
// Function:  multiplex MAC with symmetric configurability
// Notes:     clock gating outside generate statement
//-----------------------------------------------------


module mac_multiplex (clk, rst, accu_rst, config_aw, config_sc, w, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8;
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for each accumulator
	parameter  CONFIG_AW_WIDTH = 2; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+(2**CONFIG_AW_WIDTH)*PLUS_WIDTH;
	localparam M_WIDTH         = A_WIDTH+W_WIDTH;          // bitwidth of the multiplier
	localparam BLOCK_NB        = 2**CONFIG_AW_WIDTH;       // number of partial products
	localparam PS_LEVEL_NB     = CONFIG_AW_WIDTH+1;        // number of levels of partial sums
	localparam BLOCK_WIDTH     = W_WIDTH/BLOCK_NB;         // bitwidth of mini unsigned a operands
	localparam BLOCK_LEVEL_NB  = $clog2(BLOCK_WIDTH);      // addition levels inside mini partial sum tree
	localparam CONFIG_SC_WIDTH = 2**(CONFIG_AW_WIDTH+1)-1; // 1-bit signal per clock-gated block
	
	//-------------Inputs----------------------------------
	
	// basic
	input                        clk;
	input                        rst;
	input                        accu_rst;
	
	// precision config
	input  [CONFIG_AW_WIDTH-1:0] config_aw; // LSB clock-gates LSBs
	input  [CONFIG_SC_WIDTH-1:0] config_sc; // external FSM with 1-hot encoding
	
	// operands
	input          [W_WIDTH-1:0] w; // signed configurable bitwidth
	input          [A_WIDTH-1:0] a; // unsigned configurable bitwidth
	
	//-------------Outputs---------------------------------
	output reg     [Z_WIDTH-1:0] z;
	logic          [Z_WIDTH-1:0] z_tmp;
	
	//-------------Internal signals------------------------
	
	// gated operands for partial products of each level
	wire           [W_WIDTH-1:0] w_lvl       [0:BLOCK_NB-1];
	
	// partial products and sums
	logic  [W_WIDTH+A_WIDTH-1:0] ps          [0:$clog2(A_WIDTH)][0:A_WIDTH-1];
	logic  [W_WIDTH+A_WIDTH-1:0] ps_integer  [0:$clog2(A_WIDTH)][0:A_WIDTH-1]; // debug
	
	// multiplier register
	reg    [A_WIDTH+W_WIDTH-1:0] mult;
	logic  [A_WIDTH+W_WIDTH-1:0] mult_tmp;
	
	// accumulator
	logic [M_WIDTH/BLOCK_NB-1:0] mult_block  [0:BLOCK_NB-1]; // mini mult with sign compensation
	logic                        mult_co     [0:BLOCK_NB-1]; // mini mult carry-out
	logic                        mult_ci     [0:BLOCK_NB-1]; // mini mult carry-out
	logic                        mult_pad    [0:BLOCK_NB-1]; // mini mult gated padding value
	logic [Z_WIDTH/BLOCK_NB-1:0] z_div       [0:BLOCK_NB-1];
	logic [Z_WIDTH/BLOCK_NB-1:0] accu        [0:BLOCK_NB-1];
	logic                        accu_ci     [0:BLOCK_NB-1];
	logic          [Z_WIDTH-1:0] z_unpack    [0:BLOCK_NB-1];
	
	// gated clocks
	logic         [BLOCK_NB-2:0] clk_awconfig;

	// sign-compensation/gating debugger
	integer                      sc_matrix   [0:CONFIG_SC_WIDTH-1][0:CONFIG_SC_WIDTH-1]; // debug
	integer                      sc_index    [0:BLOCK_NB-1]; // debug
	integer                      gc_index    [0:BLOCK_NB-1]; // debug
	logic                        sign_active [0:BLOCK_NB-1]; // debug
	logic                        gate_active [0:BLOCK_NB-1]; // debug
	logic                        link_active [0:BLOCK_NB-1]; // debug
	
	//-------------Functions-------------------------------
	
	// max
	function int max (int a, int b);
		begin
			max = (a > b) ? a : b;
		end
	endfunction
	
	// max
	function int min (int a, int b);
		begin
			min = (a < b) ? a : b;
		end
	endfunction
	
	// sign compensation among partial products
	function int config_compensation (int i, int j);
		integer comp;
		integer value;
		begin
			comp = -1;
			for (int n=1; n<2**i+1; n=2*n) begin
				value = ((i % n)+1)/n;
				comp = comp + n * value * //$ceil(((i % n)+1)/n) * 
					(max(min(j-i+n-1,0),-1)+1) * // remove upper part with threshold
					(max(min(i-j,0),-1)+1);      // remove all lower part
			end
			config_compensation = comp;
		end
	endfunction
	
	// log2
	function int customlog2 ([31:0] value);
		integer i;
		reg [31:0] j;
		begin
			j = value - 1;
			customlog2 = 0;
			for (i = 0; i < 31; i = i + 1)
				if (j[i]) customlog2 = i+1;
		end
	endfunction
	
	// sign compensation on final sums
	function int config_index (int i);
		integer size;
		begin
			size = BLOCK_NB;
			while ( (i+1) % size != 0 ) size = size/2;
			config_index = CONFIG_AW_WIDTH-1-customlog2(size);
		end
	endfunction
	
	//-------------Debug-----------------------------------
	
	// debug for sign compensation matrix
	generate
		for (genvar i=0; i<CONFIG_SC_WIDTH; i++) begin : gen_db_lvl
			for (genvar j=0; j<CONFIG_SC_WIDTH; j++) begin : gen_db_block
				assign sc_matrix[i][j] = config_compensation(i,j);
			end
		end
	endgenerate
	
	// debug for config index
	generate
		for (genvar block=0; block<BLOCK_NB; block++) begin : gen_db_indexes
			assign sc_index[block]    = config_index(2*block+1);
			assign gc_index[block]    = config_index(block);
		end
	endgenerate
	
	//-------------Datapath--------------------------------
	
	// multiplication flip-flops
	always_ff @(posedge clk) begin
		if (rst == 1) begin
			mult <= 0;
		end
		else begin
			mult <= mult_tmp;
		end
	end
	//assign mult = mult_tmp; // non-pipelined mode
	
	// clock gatings
	generate
		for (genvar i=0; i<BLOCK_NB-1; i++) begin : gen_cg
			assign clk_awconfig[i] = clk & config_aw[config_index(i)];
		end
	endgenerate
	
	// accumulation flip-flops with clock gating
	generate
		for (genvar block=0; block<BLOCK_NB; block++) begin : gen_accu
			// never-gated first-part sub-block
			always_ff @(posedge clk) begin
				if (rst == 1 || accu_rst == 1)
					z        [block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB] <= 0;
				else
					z        [block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB] <=
						z_tmp[block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB];
			end
			// debug
			//assign gate_active[block] = ~config_aw[config_index(block)]; // gating of current block is active?
			// end-part sub-block
			if (block == BLOCK_NB-1)
				// never clock gated
				always_ff @(posedge clk) begin
					if (rst == 1 || accu_rst == 1)
						z        [(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB] <= 0;
					else
						z        [(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB] <=
							z_tmp[(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB];
				end
			else begin
				// clock gated
				always_ff @(posedge clk_awconfig[block]) begin
					if (rst == 1 || accu_rst == 1)
						z        [(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB] <= 0;
					else
						z        [(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB] <=
							z_tmp[(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB+M_WIDTH/BLOCK_NB];
				end
			end
		end
	endgenerate
	
	// unsigned mini-operand gating with config_aw signal
	generate
		for (genvar level=0; level<BLOCK_NB; level++) begin : gen_w_lvl
			for (genvar block=0; block<BLOCK_NB; block++) begin : gen_w_block
				if ($clog2((level ^ block)+1) == 0)
					assign w_lvl[level][(block+1)*BLOCK_WIDTH-1:block*BLOCK_WIDTH] = // no gating
						w[(block+1)*BLOCK_WIDTH-1:block*BLOCK_WIDTH];
				else
					assign w_lvl[level][(block+1)*BLOCK_WIDTH-1:block*BLOCK_WIDTH] = // gating
						(config_aw[CONFIG_AW_WIDTH-$clog2((level ^ block)+1)]) ?
						{BLOCK_WIDTH{1'b0}} : w[(block+1)*BLOCK_WIDTH-1:block*BLOCK_WIDTH];
			end
		end
	endgenerate

	// partial products with sign compensation
	generate
		for (genvar level=0; level<BLOCK_NB; level++) begin : gen_pp_lvl
			// partial products
			for (genvar width=0; width<BLOCK_WIDTH; width++) begin : gen_pp_width
				always_comb begin
					ps[0][level*BLOCK_WIDTH+width][W_WIDTH:0] = {1'b0, w_lvl[level] & {W_WIDTH{a[level*BLOCK_WIDTH+width]}}};
					// sign compensation
					for (int block=0; block<BLOCK_NB; block++) begin : gen_pp_comp
						if (level == BLOCK_NB-1 && block == BLOCK_NB-1) // always compensation
							ps[0][level*BLOCK_WIDTH+width][(block+1)*BLOCK_WIDTH-1] =
								~ps[0][level*BLOCK_WIDTH+width][(block+1)*BLOCK_WIDTH-1];
						else 
						if (config_compensation(block,level) != -1) begin // -1 no compensation
							ps[0][level*BLOCK_WIDTH+width][(block+1)*BLOCK_WIDTH-1] =
								(config_sc[config_compensation(block,level)]) ?
								~ps[0][level*BLOCK_WIDTH+width][(block+1)*BLOCK_WIDTH-1] : // enabled compensation
								ps[0][level*BLOCK_WIDTH+width][(block+1)*BLOCK_WIDTH-1];   // disabled compensation
						end
					end
					ps_integer[0][level*BLOCK_WIDTH+width] = $signed(ps[0][level*BLOCK_WIDTH+width][W_WIDTH:0]);
				end
			end		
		end
	endgenerate

	// adder tree with externally-computed sign compensation with config_sc signals
	generate
		for (genvar level=1; level<$clog2(A_WIDTH)+1; level++) begin : gen_add_lvl // pp level 0
			for (genvar adder=0; adder<A_WIDTH/(2*level); adder++) begin : gen_adder
				assign ps[level][adder][W_WIDTH+(2**level)-1:0] =
					$unsigned( ps[level-1][2*adder]  [W_WIDTH+(2**(level-1))-1:0]) +
					$unsigned({ps[level-1][2*adder+1][W_WIDTH+(2**(level-1))-1:0], {(2**(level-1)){1'b0}}});
				assign ps_integer[level][adder] = $signed(ps[level][adder][W_WIDTH+(2**level)-1:0]); // debug
			end
		end
	endgenerate
	assign mult_tmp = ps[$clog2(A_WIDTH)][0][W_WIDTH+A_WIDTH-1:0];
	
	// chained mini accumulators with gating
	generate
		for (genvar block=0; block<BLOCK_NB; block++) begin : gen_acc_block
			// debug
			//assign sign_active[block] = config_aw[config_index(2*block+1)];  // end sign comp is active?
			//assign link_active[block] = ~config_aw[config_index(block-1)];	 // link from previous block is active?
			// mult carry link
			if (block == 0)
				// non-connected first block
				assign mult_ci[block] = 0;
			else
				// connected if joined computation
				assign mult_ci[block] = (config_aw[config_index(block-1)]) ? 0 : mult_co[block-1];
			// sign compensation on mini mult
			if (config_index(2*block+1) == -1)
				assign {mult_co[block], mult_block[block]} = // always end comp
					mult[(block+1)*M_WIDTH/BLOCK_NB-1:block*M_WIDTH/BLOCK_NB] +
					$unsigned(mult_ci[block]) +                                           // mult carry-in
					($unsigned(config_aw[CONFIG_AW_WIDTH-1]) << M_WIDTH/(2*BLOCK_NB)-1) + // mid comp for min bits
					($unsigned(1) << M_WIDTH/BLOCK_NB-1);                                 // end comp always
			else
				assign {mult_co[block], mult_block[block]} =
					mult[(block+1)*M_WIDTH/BLOCK_NB-1:block*M_WIDTH/BLOCK_NB] +
					$unsigned(mult_ci[block]) +                                            // mult carry-in
					($unsigned(config_aw[CONFIG_AW_WIDTH-1]) << M_WIDTH/(2*BLOCK_NB)-1) +  // mid comp for min bits
					($unsigned(config_aw[config_index(2*block+1)]) << M_WIDTH/BLOCK_NB-1); // end comp (variable)
			// accu carry link
			if (block == 0)
				// non-connected first block
				assign accu_ci[block] = 0;
			else
				// connected if joined computation
				assign accu_ci[block] = (config_aw[config_index(block-1)]) ? 0 : accu[block-1][M_WIDTH/BLOCK_NB];
			// padding mult_block
			if (block == BLOCK_NB-1)
				// always padded last block
				assign mult_pad[block] = mult_block[block][M_WIDTH/BLOCK_NB-1];
			else
				// variable padding if block used
				assign mult_pad[block] = mult_block[block][M_WIDTH/BLOCK_NB-1] && config_aw[config_index(block)];
			// accumulator
			assign accu[block][Z_WIDTH/BLOCK_NB-1:0] =
				z[(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB] + // already in accumulator
				$unsigned(accu_ci[block]) +                              // carry-in from previous block
				$unsigned(mult_block[block]) +                           // new value
				({PLUS_WIDTH{mult_pad[block]}} << M_WIDTH/BLOCK_NB);     // padding if mode used
				//{{PLUS_WIDTH{mult_block[block][M_WIDTH/BLOCK_NB-1]}}, mult_block[block]}; // padded new value
			assign z_div[block] = accu[block][Z_WIDTH/BLOCK_NB-1:0];
			// accumulator output
			assign z_tmp[(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB] =
				accu[block][Z_WIDTH/BLOCK_NB-1:0];
			//assign z_unpack[(block+1)*Z_WIDTH/BLOCK_NB-1:block*Z_WIDTH/BLOCK_NB] =
			//	accu[block][Z_WIDTH/BLOCK_NB-1:0];
		end
	endgenerate
	
endmodule // mac_multiplex

