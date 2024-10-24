//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    mac_serial
// Function:  multibit-serial MAC with w-configurability with clock-gating
// Notes:     accu secondary clk but kept fsm_accu signal
// Version:   1.9
//-----------------------------------------------------


module mac_serial (clk, clk_accu, rst, config_w, fsm_last, fsm_accu, w_serial, a, z);

	//-------------Parameters------------------------------
	parameter  W_WIDTH        = 8; // max bits for w
	parameter  A_WIDTH        = 8;
	parameter  PLUS_WIDTH     = 4; // extra for the MAC accumulator
	parameter  N_WIDTH        = 2;
	parameter  CONFIG_W_WIDTH = 2; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH        = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	localparam PS_LEVEL_NB    = $clog2(N_WIDTH+1);   // number of levels of partial sums
	
	//-------------Inputs----------------------------------
	
	// basic
	input                       clk;
	input                       clk_accu;
	input                       rst;
	
	// config (externally registered)
	input  [CONFIG_W_WIDTH-1:0] config_w;    // LSB clock-gates LSBs
	
	// MAC FSM (externally registered)
	input                       fsm_last;
	input                       fsm_accu;
	
	// operands
	input         [N_WIDTH-1:0] w_serial;    // signed bit-serial from LSB to MSB
	input         [A_WIDTH-1:0] a;           // unsigned
	
	//-------------Outputs---------------------------------
	output reg    [Z_WIDTH-1:0] z;           // signed
	logic         [Z_WIDTH-1:0] z_tmp;
	
	//-------------Internal signals------------------------
	reg   [A_WIDTH+W_WIDTH-1:0] mult_accu;
	logic [A_WIDTH+W_WIDTH-1:0] mult_accu_tmp;
	logic [A_WIDTH+N_WIDTH-1:0] psum;
	logic [A_WIDTH+N_WIDTH-1:0] ps         [0:PS_LEVEL_NB-1][0:N_WIDTH-1];
	logic [A_WIDTH+N_WIDTH-1:0] ps_integer [0:PS_LEVEL_NB-1][0:N_WIDTH-1]; // debug
	logic  [CONFIG_W_WIDTH-1:0] clk_cg;
	logic  [CONFIG_W_WIDTH-1:0] clk_accu_cg;
	
	//-------------Datapath--------------------------------
	
	// clock gating
	assign clk_cg      = {CONFIG_W_WIDTH{clk}}      & ~config_w;
	assign clk_accu_cg = {CONFIG_W_WIDTH{clk_accu}} & ~config_w;
	
	// mult flip-flops never clock-gated
	always_ff @(posedge clk) begin
		if (rst == 1) begin
			mult_accu            [A_WIDTH+W_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)] <= 0;
		end
		else begin
			mult_accu            [A_WIDTH+W_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)]
				<= mult_accu_tmp [A_WIDTH+W_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)];
		end
	end
	
	// mult flip-flops with clock-gating
	generate
		for (genvar i=0; i<=CONFIG_W_WIDTH-1; i++) begin
			always_ff @(posedge clk_cg[i]) begin
				if (rst == 1) begin
					mult_accu            [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)] <= 0;
				end
				else begin
					mult_accu            [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)]
						<= mult_accu_tmp [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)];
				end
			end
		end
	endgenerate
		
	// accu flip-flops never clock-gated
	always_ff @(posedge clk_accu) begin
		if (rst == 1) begin
			z                    [Z_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)]         <= 0;
		end
		else begin
			z                    [Z_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)]
				<= z_tmp         [Z_WIDTH-1:W_WIDTH-W_WIDTH/(2**CONFIG_W_WIDTH)];
		end
	end
	
	// accu flip-flops with clock-gating
	generate
		for (genvar i=0; i<=CONFIG_W_WIDTH-1; i++) begin
			always_ff @(posedge clk_accu_cg[i]) begin
				if (rst == 1) begin
					z                    [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)] <= 0;
				end
				else begin
					z                    [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)]
						<= z_tmp         [W_WIDTH-W_WIDTH/(2**(i+1))-1:W_WIDTH-W_WIDTH/(2**i)];
				end
			end
		end
	endgenerate
	
	// partial products
	generate
		for (genvar pprod=0; pprod<N_WIDTH; pprod++) begin : gen_pp
			if (pprod < N_WIDTH-1)
				// positive pprod only
				assign ps[0][pprod][A_WIDTH:0] = (w_serial[pprod]) ? a : 0;
			else
				// last pprod can be negative
				always_comb begin
					if (w_serial[pprod])
						ps[0][N_WIDTH-1][A_WIDTH:0] = (fsm_last) ? -a : a;
					else
						ps[0][N_WIDTH-1][A_WIDTH:0] = 0;
				end
			assign ps_integer[0][pprod] = $signed(ps[0][pprod][A_WIDTH:0]);
		end
	endgenerate
	
	// adder tree for current partial product
	generate
		for (genvar level=1; level<PS_LEVEL_NB; level++) begin : gen_level // pp level 0
			for (genvar add=0; add<N_WIDTH/(2*level); add++) begin : gen_add
				assign ps[level][add][A_WIDTH+(2**level)-1:0] = 
					$unsigned( ps[level-1][2*add]  [A_WIDTH+(2**(level-1))-1:0]) +
					$unsigned({ps[level-1][2*add+1][A_WIDTH+(2**(level-1))-1:0], {(2**(level-1)){1'b0}}});
				assign ps_integer[level][add] = $signed(ps[level][add][A_WIDTH+(2**level)-1:0]); // debug
			end
		end
	endgenerate
	
	// partial sum and MAC accumuation (no accu padding: always positive (only last pprod can be negative)
	always_comb begin
		// partial sum with accumulation
		psum = (fsm_accu) ? ps[PS_LEVEL_NB-1][0][A_WIDTH+N_WIDTH-1:0] : ps[PS_LEVEL_NB-1][0][A_WIDTH+N_WIDTH-1:0] + mult_accu[A_WIDTH+W_WIDTH-1:W_WIDTH];
		// multiplier accumulator with shifting
		mult_accu_tmp[A_WIDTH+W_WIDTH-1:W_WIDTH-N_WIDTH] = psum;
		mult_accu_tmp[W_WIDTH-N_WIDTH-1:0] = mult_accu[W_WIDTH-1:N_WIDTH];
		// MAC accumulator
		z_tmp = $signed(z) + $signed(mult_accu); // (fsm_accu) ? $signed(z) + $signed(mult_accu) : $signed(z);
	end
	
endmodule // mac_serial

