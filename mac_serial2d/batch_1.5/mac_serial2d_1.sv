//-------------------------------------------------------------
// Design:        2D bit-serial MAC wrap with input register
// Description:   2D bit-serial MAC unit from Loom
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0000 -> 8x8b
//                mode 0111 -> 4x4b
//                mode 1111 -> 2x2b
//                mode 0001 -> 8x4b
//                mode 0011 -> 8x2b       
// Author:	      Linyan Mei
//-------------------------------------------------------------


module top_mac_serial2d (clk_fast, clk_slow, rst, rst_mult, mode, w_sel, a_sel, shift_ctr, sign_ctr, w, a, z);

	//-------------Parameters------------------------------

	
	//-------------Local parameters------------------------

	
	//-------------Inputs----------------------------------
	
	// basic
	input                       clk_fast;
	input                       clk_slow;
	input                       rst;
	input                       rst_mult;
	
	// config 
	input                 [3:0] mode;   
	
	// operands
	input                 [7:0] w;        // signed
	input                 [7:0] a;        // unsigned

	// FSM
	input                 [2:0] w_sel;         //              weight select signal from FSM
	input                 [2:0] a_sel;         //          activation select signal from FSM
	input                       shift_ctr;     //              shift control signal from FSM
	input                       sign_ctr;      //               sign control signal from FSM
	
	//-------------Outputs---------------------------------
	output reg           [19:0] z;        // signed
	
	//-------------Internal signals------------------------
	reg		                    rst_reg;
	reg		                    rst_mult_reg;
	reg		              [7:0] w_reg;
	reg		              [7:0] a_reg;

	reg                   [2:0] w_sel_reg;
	reg                   [2:0] a_sel_reg;
	reg                         shift_ctr_reg;
	reg                         sign_ctr_reg;
	
	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	mac_serial2d #(
		// Parameters

	) mac (

		// Inputs
		.clk_fast    (clk_fast),
		.clk_slow    (clk_slow), 
		.rst         (rst_reg),
		.rst_mult    (rst_mult_reg),
		.mode        (mode),
		.shift_ctr   (shift_ctr_reg), 
		.sign_ctr    (sign_ctr_reg),
		.w_sel       (w_sel_reg),
		.a_sel       (a_sel_reg), 
		.w           (w_reg),
		.a           (a_reg),

		// Outputs
		.z          (z)
	);	

	// synchronous rst of the MAC module
	always_ff @(posedge clk_fast)
		rst_reg <= rst;

	always_ff @(posedge clk_fast)
		rst_mult_reg <= rst_mult;

	// input registers
	always_ff @(posedge clk_fast) begin
		if (rst == 1) begin
			shift_ctr_reg     <= 0;
			sign_ctr_reg      <= 0;
			w_sel_reg         <= 0;
			a_sel_reg         <= 0;
			w_reg             <= 0;
			a_reg             <= 0;
		end
		else begin
			shift_ctr_reg     <= shift_ctr;
			sign_ctr_reg      <= sign_ctr;
			w_sel_reg         <= w_sel;
			a_sel_reg         <= a_sel;
			w_reg             <= w;
			a_reg             <= a;
		end
	end

	
endmodule // top_mac_serial2d

//-------------------------------------------------------------
// Design:        2D bit-serial MAC wrap without input register and FSM
// Description:   2D bit-serial MAC unit from Loom
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0000 -> 8x8b
//                mode 0111 -> 4x4b
//                mode 1111 -> 2x2b
//                mode 0001 -> 8x4b
//                mode 0011 -> 8x2b       
// Author:	      Linyan Mei
//-------------------------------------------------------------


module mac_serial2d (clk_fast, clk_slow, rst, rst_mult, mode, shift_ctr, sign_ctr, w_sel, a_sel, w, a, z);

	//-------------Parameters------------------------------

	
	//-------------Local parameters------------------------

	
	//-------------Inputs----------------------------------
	
	// basic
	input                       clk_fast;
	input                       clk_slow;
	input                       rst;
	input                       rst_mult;
	
	// config
	input                 [3:0] mode;   
	
	// MAC FSM (externally registered)
	input                       shift_ctr;
	input                       sign_ctr;
	input                 [2:0] w_sel;
	input                 [2:0] a_sel;
	
	// operands
	input                 [7:0] w;    // signed
	input                 [7:0] a;    // unsigned

	
	//-------------Outputs---------------------------------
	output reg           [19:0] z;           // signed
	logic                [19:0] z_tmp;
	
	//-------------Internal signals------------------------
	logic                       w_serial;    // signed bit-serial from LSB to MSB
	logic                       a_serial;    // unsigned

	reg                  [ 4:0] mult_accu_c;
	reg                  [14:0] mult_accu_r;

	logic                [ 4:0] mult_accu_c_tmp0;
	logic                [ 4:0] mult_accu_c_tmp; // shifted version of mult_accu_c_tmp0
	logic                [14:0] mult_accu_r_tmp;

	logic                       ps;
	logic                [ 3:0] clk_fast_cg;   
	logic                [ 3:0] clk_slow_cg;   
	
	//-------------Datapath--------------------------------
	
	// clock gating
	assign clk_fast_cg = {4{clk_fast}} & ~mode;
	assign clk_slow_cg = {4{clk_slow}} & ~mode;
	

	//------------------------------------------------------------	
	// mult carry & result flip-flops never clock-gated
	always_ff @(posedge clk_fast) begin
		if (rst == 1) begin
			mult_accu_r[14:12] <= 0;
			mult_accu_c <= 0;
		end
		else begin
			mult_accu_r[14:12] <= mult_accu_r_tmp [14:12];
			mult_accu_c <= mult_accu_c_tmp;
		end
	end

	
	// mult result flip-flops with clock-gating
	always_ff @(posedge clk_fast_cg[3]) begin
		if (rst == 1) begin
			mult_accu_r[11:8] <= 0;
		end
		else begin
			mult_accu_r[11:8] <= mult_accu_r_tmp [11:8];
		end
	end

	always_ff @(posedge clk_fast_cg[2]) begin
		if (rst == 1) begin
			mult_accu_r[7:6] <= 0;
		end
		else begin
			mult_accu_r[7:6] <= mult_accu_r_tmp [7:6];
		end
	end

	always_ff @(posedge clk_fast_cg[1]) begin
		if (rst == 1) begin
			mult_accu_r[5:4] <= 0;
		end
		else begin
			mult_accu_r[5:4] <= mult_accu_r_tmp [5:4];
		end
	end

	always_ff @(posedge clk_fast_cg[0]) begin
		if (rst == 1) begin
			mult_accu_r[3:0] <= 0;
		end
		else begin
			mult_accu_r[3:0] <= mult_accu_r_tmp [3:0];
		end
	end


	//------------------------------------------------------------	
	// accu flip-flops never clock-gated
	always_ff @(posedge clk_slow) begin
		if (rst == 1) begin
			z[19:12] <= 0;
		end
		else begin
			z[19:12] <= z_tmp[19:12];
		end
	end
	
	// accu flip-flops with clock-gating
	always_ff @(posedge clk_slow_cg[3]) begin
		if (rst == 1) begin
			z[11:8] <= 0;
		end
		else begin
			z[11:8] <= z_tmp[11:8];
		end
	end

	always_ff @(posedge clk_slow_cg[2]) begin
		if (rst == 1) begin
			z[7:6] <= 0;
		end
		else begin
			z[7:6] <= z_tmp[7:6];
		end
	end

	always_ff @(posedge clk_slow_cg[1]) begin
		if (rst == 1) begin
			z[5:4] <= 0;
		end
		else begin
			z[5:4] <= z_tmp[5:4];
		end
	end

	always_ff @(posedge clk_slow_cg[0]) begin
		if (rst == 1) begin
			z[3:0] <= 0;
		end
		else begin
			z[3:0] <= z_tmp[3:0];
		end
	end


	//------------------------------------------------------------	
	// input select
	always_comb begin
		case (w_sel)
			3'b000: w_serial = w[0];
			3'b001: w_serial = w[1];
			3'b010: w_serial = w[2];
			3'b011: w_serial = w[3];
			3'b100: w_serial = w[4];
			3'b101: w_serial = w[5];
			3'b110: w_serial = w[6];
			3'b111: w_serial = w[7];
			default: w_serial = w[0];
		endcase
	end	

	always_comb begin
		case (a_sel)
			3'b000: a_serial = a[0];
			3'b001: a_serial = a[1];
			3'b010: a_serial = a[2];
			3'b011: a_serial = a[3];
			3'b100: a_serial = a[4];
			3'b101: a_serial = a[5];
			3'b110: a_serial = a[6];
			3'b111: a_serial = a[7];
			default: a_serial = a[0];
		endcase
	end	

	// partial products	
	always_comb begin

		// --- ps ---
		ps = w_serial & a_serial;

		// --- mult_accu_c_tmp ---
		if (!rst_mult)
			if (!sign_ctr)
				mult_accu_c_tmp0 = mult_accu_c + ps;
			else
				mult_accu_c_tmp0 = mult_accu_c - ps;
		else
			if (!sign_ctr)
				mult_accu_c_tmp0 = ps;
			else
				mult_accu_c_tmp0 = - ps;

		if (shift_ctr)
			mult_accu_c_tmp = {mult_accu_c_tmp0[4],mult_accu_c_tmp0[4:1]};
		else
			mult_accu_c_tmp = mult_accu_c_tmp0;

		// --- mult_accu_r_tmp ---
		if (shift_ctr)
			mult_accu_r_tmp = {mult_accu_c_tmp0[0],mult_accu_r[14:1]};
		else
			mult_accu_r_tmp = mult_accu_r;
	end
	
	// results accumulation
	always_comb begin
		if (rst_mult)
			z_tmp = $signed(z) + $signed({mult_accu_c[1:0],mult_accu_r[14:1]});
		else
			z_tmp = '0;
	end
	
endmodule // mac_serial2d

