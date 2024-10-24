//-------------------------------------------------------------
// Design:        2D multi_4bit-serial MAC wrap with input register
// Description:   2D multi_4bit-serial MAC unit from Loom
// Version:       1.5
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 000 -> 8x8b
//                mode 111 -> 4x4b
//                mode 001 -> 8x4b    
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
	input                 [2:0] mode;   
	
	// operands
	input                 [7:0] w;        // signed
	input                 [7:0] a;        // unsigned

	// FSM
	input                       w_sel;         //              weight select signal from FSM
	input                       a_sel;         //          activation select signal from FSM
	input                       shift_ctr;     //              shift control signal from FSM
	input                       sign_ctr;      //               sign control signal from FSM
	
	//-------------Outputs---------------------------------
	output reg           [19:0] z;        // signed
	
	//-------------Internal signals------------------------
	reg		                    rst_reg;
	reg		                    rst_mult_reg;
	reg		              [7:0] w_reg;
	reg		              [7:0] a_reg;

	reg                         w_sel_reg;
	reg                         a_sel_reg;
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
// Design:        2D multi-bit(4b)-serial MAC wrap without input register and FSM
// Description:   2D multi-bit(4b)-serial MAC unit from Loom
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 000 -> 8x8b
//                mode 111 -> 4x4b
//                mode 001 -> 8x4b       
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
	
	// config (externally registered)
	input                 [2:0] mode;   
	
	// MAC FSM (externally registered)
	input                       shift_ctr;
	input                       sign_ctr;
	input                       w_sel;
	input                       a_sel;
	
	// operands
	input                 [7:0] w;    // signed
	input                 [7:0] a;    // unsigned

	
	//-------------Outputs---------------------------------
	output reg           [19:0] z;           // signed
	logic                [19:0] z_tmp;
	
	//-------------Internal signals------------------------
	logic                 [3:0] w_serial;    // signed bit-serial from LSB to MSB
	logic                 [3:0] a_serial;    // unsigned

	logic                 [3:0] w_serial_in;    // w_serial after select enable
	logic                 [3:0] a_serial_in;    // a_serial after select enable

	reg                  [ 9:0] mult_accu_c;
	reg                  [11:0] mult_accu_r;

	logic                [ 9:0] mult_accu_c_tmp0;
	logic                [ 9:0] mult_accu_c_tmp; // shifted version of mult_accu_c_tmp0
	logic                [11:0] mult_accu_r_tmp;

	logic                [ 8:0] ps;
	logic                [ 2:0] clk_fast_cg;   
	logic                [ 2:0] clk_slow_cg;   
	
	//-------------Datapath--------------------------------
	
	// clock gating
	assign clk_fast_cg = {3{clk_fast}} & ~mode;
	assign clk_slow_cg = {3{clk_slow}} & ~mode;
	

	//------------------------------------------------------------	
	// mult carry & result flip-flops never clock-gated
	always_ff @(posedge clk_fast) begin
		if (rst == 1) begin
			mult_accu_r[11:8] <= 0;
			mult_accu_c <= 0;
		end
		else begin
			mult_accu_r[11:8] <= mult_accu_r_tmp [11:8];
			mult_accu_c <= mult_accu_c_tmp;
		end
	end

	
	// mult result flip-flops with clock-gating
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
			z[19:8] <= 0;
		end
		else begin
			z[19:8] <= z_tmp[19:8];
		end
	end
	
	// accu flip-flops with clock-gating
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
			1'b0: w_serial = {w[3],w[2],w[1],w[0]};
			1'b1: w_serial = {w[7],w[6],w[5],w[4]};
			default: w_serial = {w[3],w[2],w[1],w[0]};
		endcase
	end	

	always_comb begin
		case (a_sel)
			1'b0: a_serial = {a[3],a[2],a[1],a[0]};
			1'b1: a_serial = {a[7],a[6],a[5],a[4]};
			default: a_serial = {a[3],a[2],a[1],a[0]};
		endcase
	end	

	// partial products	
	always_comb begin

		// --- ps ---
		if (!sign_ctr)
			ps = $signed({1'b0,w_serial}) * $signed({1'b0,a_serial});
		else
			ps = $signed(w_serial) * $signed({1'b0,a_serial});

		// --- mult_accu_c_tmp ---
		if (!rst_mult)
			mult_accu_c_tmp0 = $signed(mult_accu_c) + $signed(ps);
		else
			mult_accu_c_tmp0 = $signed(ps);

		if (shift_ctr)
			mult_accu_c_tmp = {{3{mult_accu_c_tmp0[9]}},mult_accu_c_tmp0[9:4]};
		else
			mult_accu_c_tmp = mult_accu_c_tmp0;

		// --- mult_accu_r_tmp ---
		if (shift_ctr)
			mult_accu_r_tmp = {mult_accu_c_tmp0[3:0],mult_accu_r[11:4]};
		else
			mult_accu_r_tmp = mult_accu_r;
	end	
	
	// results accumuation
	always_comb begin
		if (rst_mult)
			z_tmp = $signed(z) + $signed({mult_accu_c[7:0],mult_accu_r[11:4]});
		else
			z_tmp = '0;
	end	

	
endmodule // mac_serial2d

