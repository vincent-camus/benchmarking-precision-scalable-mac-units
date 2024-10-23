//-------------------------------------------------------------
// Design:        bfusion1D_1_level MAC wrap with input register
// Description:   1D 1-level BitFusion MAC unit
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0 -> #1  8x8b
//                mode 1 -> #2  8x4b
// Author:	      Linyan Mei
//-------------------------------------------------------------

module top_mac_bfusion1d (clk, rst, accu_rst, a, w, mode, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				          clk;
	input 				          rst;
	input 				          accu_rst;

	//----Data in--------
	input         [15:0]          a;           // unsigned activation 
	input         [ 7:0]          w;           // signed / unsigned weight 

	//----Control in-----
	input                         mode;              

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	reg                           rst_reg;
	reg                           accu_rst_reg;

	reg           [15:0]          a_reg;
	reg           [ 7:0]          w_reg;

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	mac_bfusion1d #(
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
		.mode       (mode),
		// Outputs
		.z          (z)
	);


	// synchronous rst of the MAC module
	always_ff @(posedge clk)
		rst_reg <= rst;

	always_ff @(posedge clk)
		accu_rst_reg <= accu_rst;

	// input registers
	always_ff @(posedge clk) begin
		if (rst == 1) begin
			w_reg             <= '0;
			a_reg             <= '0;

		end
		else begin
			w_reg             <= w;
			a_reg             <= a;
		end
	end

endmodule


//-------------------------------------------------------------
// Design:        1D bfusion_1_level MAC wrap without input register
// Description:   1D 1-level BitFusion MAC unit
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                mode 1 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register 
// Author:	      Linyan Mei
//-------------------------------------------------------------

module mac_bfusion1d (clk, rst, accu_rst, a, w, mode, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				 clk, rst, accu_rst;

	//----Data in--------
	input         [15:0] a ;           // unsigned activation 
	input         [ 7:0] w ;           // signed / unsigned weight 

	//----Control in-----
	input                mode;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	logic        [1:0][7:0] a_wrap;  // signed
	logic        [1:0][3:0] w_wrap;  // unsigned



	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitFusion #(
		// Parameters
		.HEADROOM   (HEADROOM)
	)
	BitFusion (
		// Inputs
		.clk        (clk),
		.rst        (rst),
		.accu_rst   (accu_rst),
		.a          (a_wrap),
		.w          (w_wrap),
		.mode       (mode),
		// Outputs
		.z          (z)
	);


	//---------data rearrangement and dispatch--------
	always_comb begin
		unique case (mode)
			// 88
			1'b0: begin 
						a_wrap = {{a[7:0]},{a[7:0]}};

						w_wrap = {{w[7:4]},{w[3:0]}};
					end

			// 84
			1'b1: begin 
						a_wrap = {{a[15:8]},{a[7:0]}};

						w_wrap = {{w[7:4]},{w[3:0]}};
					end

		endcase
	end	

endmodule // bfusion1D_1_level



//-------------------------------------------------------------
// Design:        BitFusion
// Description:   1D BitFusion with output register
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0 -> #1  8x8b
//                mode 1 -> #2  8x4b
//-------------------------------------------------------------

module BitFusion (clk, rst, accu_rst, a, w, mode, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------
	//----basic in--------
	input 		  clk, rst, accu_rst;

	//----Data in--------
	input         [1:0][7:0] a ;           // unsigned activation
	input         [1:0][3:0] w ;           // signed / unsigned weight

	//----Control in-----
	input                    mode;

	//-------------Outputs---------------------------------
	output   reg  [15+HEADROOM:0] z ;
	logic         [15+HEADROOM:0] z_tmp;

	//-------------Internal signals-----------------------
	reg			  [15:0] mult;
	logic         [15:0] mult_tmp, p_88;

	logic 		         clk1;
	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick88 BitBrick88 (
    .a_88_1(a[1]), .a_88_2(a[0]),

	.w_88_1(w[1]), .w_88_2(w[0]),

	.mode(mode),
	.p_88(p_88)
    );


	// clock gating signal generation
	always_comb begin
		clk1 = (clk & ~mode) | (clk & rst);
	end

	// flip-flops never clock-gated
	always_ff @(posedge clk) begin
		if (rst) begin
			z    [12+HEADROOM:0]  <= 0;
			mult [12         :0]  <= 0;
		end
		else begin
			z    [12+HEADROOM:0]  <= z_tmp    [12+HEADROOM:0];
			mult [12         :0]  <= mult_tmp [12         :0];
		end
	end

	// clock-gated flip-flops ---------------------------------------
	always_ff @(posedge clk1) begin
		if (rst) begin
			z    [15+HEADROOM:13+HEADROOM]  <= 0;
			mult [15         :13         ]  <= 0;
		end
		else begin
			z    [15+HEADROOM:13+HEADROOM]  <= z_tmp    [15+HEADROOM:13+HEADROOM];
			mult [15         :13         ]  <= mult_tmp [15         :13         ];
		end
	end

	//---------------------------------------------------------------

	// logic
	always_comb begin
		unique case (mode)
			1'b0: z_tmp    = (accu_rst) ? '0 : $signed(z) + $signed({{HEADROOM{mult[15]}},mult});

			1'b1: z_tmp    = (accu_rst) ? '0 : $signed(z[12+HEADROOM:0]) + $signed({{HEADROOM{mult[12]}},mult[12:0]});
		endcase
		mult_tmp = p_88;
	end

endmodule // BitFusion


//-------------------------------------------------------------
// Design:        BitBrick88
// Description:   8x8 block for 1-level 1D-BitFusion
// Working mode:  mode 0 -> #1  8x8b
//                mode 1 -> #2  8x4b
//-------------------------------------------------------------

module BitBrick88 (a_88_1, a_88_2,
				   w_88_1, w_88_2, 
				   mode, p_88);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [7:0] a_88_1, a_88_2;             // unsigned activation  
	input         [3:0] w_88_1, w_88_2;             // signed / unsigned weight
	//----Control in-----
	input               mode;             

	//-------------Outputs---------------------------------
	output        [15:0] p_88;

	//-------------Internal signals-----------------------
	logic         [11:0] pp1, pp2;                   // partial products
	logic         [11+4:0] ex_pp1;                   // extended partial products (<<0, <<4)
	logic         [11+0:0] ex_pp2;                   // extended partial products (<<0)

	logic         [15:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	BitBrick84  BB_left (
		// Inputs
		.a_8b(a_88_1), .w_4b(w_88_1), 
		.pick_sign(1'b1),
		// Outputs
		.p_84(pp1)
	);

	BitBrick84  BB_right (
		// Inputs
		.a_8b(a_88_2), .w_4b(w_88_2), 
		.pick_sign(mode),
		// Outputs
		.p_84(pp2)
	);


	always_comb begin
		unique case (mode)
			1'b0: begin  ex_pp1 = {pp1,4'b0};                     // partial product (@ position 1) left shifts 4 bits -> extended partial product
						 ex_pp2 = pp2;                            // partial product (@ position 2) left shifts 0 bits -> extended partial product

						 psum = $signed(ex_pp1) + $signed({1'b0,ex_pp2});
					end

			1'b1: begin  ex_pp1 = {{4{pp1[11]}},pp1};             // no shift, just do sign bit extension. 
						 ex_pp2 = pp2;                   

						 psum = $signed(ex_pp1) + $signed(ex_pp2);
					end
		endcase

		
	end	

	assign p_88 = psum;

endmodule // BitBrick88



//-------------------------------------------------------------
// Design:        BitBrick84
// Description:   8x4 unit block for 1-level 1D-BitFusion
// Working mode:  Half-signed / Unsigned multiplication
//-------------------------------------------------------------

module BitBrick84 (a_8b, w_4b, pick_sign, p_84);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [7:0] a_8b;             // unsigned activation  
	input         [3:0] w_4b;             // signed / unsigned weight
	//----Control in-----
	input               pick_sign;        // half-signed(1) / unsigned(0) configuration

	//-------------Outputs---------------------------------
	output       [11:0] p_84;

	//-------------Internal signals------------------------
	logic         [4:0] w;
	
	//-------------Datapath--------------------------------

	always_comb begin		
		w = (pick_sign) ? {w_4b[3],w_4b} : {1'b0,w_4b};
	end	

	assign p_84 = $signed(w)*$signed({1'b0,a_8b});

endmodule // BitBrick84
