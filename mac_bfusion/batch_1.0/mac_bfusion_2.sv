//-------------------------------------------------------------
// Design:        BitFusion wrap top with input register
// Description:   BitFusion top level including data rearrangement and dispatch (with input register)
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 000 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                config_aw 010 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register 
//                config_aw 011 -> #16 2x2b -> activate  8 bits /  8 bits + headroom register
//                config_aw 110 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register
//                config_aw 111 -> #4  8x2b -> activate 12 bits / 12 bits + headroom register          
// Author:	      Linyan Mei
//-------------------------------------------------------------

module top_mac_bfusion (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				clk, rst, accu_rst;

	//----Data in--------
	input         [31:0] a ;           // unsigned activation 
	input         [31:0] w ;           // signed / unsigned weight 

	//----Control in-----
	input         [2:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	reg			  [31:0] a_reg;
	reg			  [31:0] w_reg;

	reg                      rst_reg;
	reg                      accu_rst_reg;

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	mac_bfusion #(
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
		.config_aw  (config_aw),
		// Outputs
		.z          (z)
	);


	// flip-flops 
	always_ff @(posedge clk) begin
		if (rst) begin
			a_reg  <= 0;
			w_reg  <= 0;
		end
		else begin
			a_reg  <= a;
			w_reg  <= w;
		end
	end
	
	// synchronous resets
	always_ff @(posedge clk) begin
		rst_reg       <= rst;
		accu_rst_reg  <= accu_rst;
	end

endmodule // top_mac_bfusion


//-------------------------------------------------------------
// Design:        BitFusion wrap without input register
// Description:   BitFusion top level including data rearrangement and dispatch
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 000 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                config_aw 010 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register 
//                config_aw 011 -> #16 2x2b -> activate  8 bits /  8 bits + headroom register
//                config_aw 110 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register
//                config_aw 111 -> #4  8x2b -> activate 12 bits / 12 bits + headroom register          
// Author:	      Linyan Mei
//-------------------------------------------------------------

module mac_bfusion (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				clk, rst, accu_rst;

	//----Data in--------
	input         [31:0] a ;           // unsigned activation 
	input         [31:0] w ;           // signed / unsigned weight 

	//----Control in-----
	input         [2:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	logic        [3:0][3:0][1:0] a_wrap;  // signed
	logic        [3:0][3:0][1:0] w_wrap;  // unsigned



	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitFusion_top #(
		// Parameters
		.HEADROOM   (HEADROOM)
	)
	BitFusion_top (
		// Inputs
		.clk        (clk),
		.rst        (rst),
		.accu_rst   (accu_rst),
		.a          (a_wrap),
		.w          (w_wrap),
		.config_aw       (config_aw),
		// Outputs
		.z          (z)
	);


	//---------data rearrangement and dispatch--------
	always_comb begin
		unique case (config_aw)
			3'b000: begin 
						a_wrap = {{a[7:6],a[7:6],a[7:6],a[7:6]},{a[5:4],a[5:4],a[5:4],a[5:4]},
							      {a[3:2],a[3:2],a[3:2],a[3:2]},{a[1:0],a[1:0],a[1:0],a[1:0]}};

						w_wrap = {{w[1:0],w[3:2],w[5:4],w[7:6]},{w[1:0],w[3:2],w[5:4],w[7:6]},
							      {w[1:0],w[3:2],w[5:4],w[7:6]},{w[1:0],w[3:2],w[5:4],w[7:6]}};
					end

			3'b010: begin 
						a_wrap = {{a[15:14],a[15:14],a[7:6],a[7:6]},{a[13:12],a[13:12],a[5:4],a[5:4]},
							      {a[11:10],a[11:10],a[3:2],a[3:2]},{a[ 9: 8],a[ 9: 8],a[1:0],a[1:0]}};

						w_wrap = {{w[13:12],w[15:14],w[5:4],w[7:6]},{w[13:12],w[15:14],w[5:4],w[7:6]},
							      {w[ 9: 8],w[11:10],w[1:0],w[3:2]},{w[ 9: 8],w[11:10],w[1:0],w[3:2]}};
					end

			3'b011: begin 
						a_wrap = {{a[31:30],a[29:28],a[27:26],a[25:24]},{a[23:22],a[21:20],a[19:18],a[17:16]},
							      {a[15:14],a[13:12],a[11:10],a[ 9: 8]},{a[ 7: 6],a[ 5: 4],a[ 3: 2],a[ 1: 0]}};

						w_wrap = {{w[31:30],w[29:28],w[27:26],w[25:24]},{w[23:22],w[21:20],w[19:18],w[17:16]},
							      {w[15:14],w[13:12],w[11:10],w[ 9: 8]},{w[ 7: 6],w[ 5: 4],w[ 3: 2],w[ 1: 0]}};
					end

			3'b110: begin 
						a_wrap = {{a[15:14],a[15:14],a[7:6],a[7:6]},{a[13:12],a[13:12],a[5:4],a[5:4]},
							      {a[11:10],a[11:10],a[3:2],a[3:2]},{a[ 9: 8],a[ 9: 8],a[1:0],a[1:0]}};

						w_wrap = {{w[5:4],w[7:6],w[1:0],w[3:2]},{w[5:4],w[7:6],w[1:0],w[3:2]},
							      {w[5:4],w[7:6],w[1:0],w[3:2]},{w[5:4],w[7:6],w[1:0],w[3:2]}};
					end

			3'b111: begin 
						a_wrap = {{a[31:30],a[23:22],a[15:14],a[7:6]},{a[29:28],a[21:20],a[13:12],a[5:4]},
							      {a[27:26],a[19:18],a[11:10],a[3:2]},{a[25:24],a[17:16],a[ 9: 8],a[1:0]}};

						w_wrap = {{w[ 7: 6],w[ 5: 4],w[ 3: 2],w[1:0]},{w[ 7: 6],w[ 5: 4],w[ 3: 2],w[1:0]},
							      {w[ 7: 6],w[ 5: 4],w[ 3: 2],w[1:0]},{w[ 7: 6],w[ 5: 4],w[ 3: 2],w[1:0]}};
					end
		endcase

		
	end	
	


endmodule // top_mac_bfusion


//-------------------------------------------------------------
// Design:        BitBrick22_v2
// Description:   2x2 unit block for BitFusion
//                by using system function $signed(...)
// Working config_aw:  Half-signed / Unsigned multiplication
// Author:	      Linyan Mei
//-------------------------------------------------------------

module BitBrick22_v2 (a_22, w_22, pick_sign, p_22);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [1:0] a_22;             // unsigned activation  
	input         [1:0] w_22;             // signed / unsigned weight
	//----Control in-----
	input               pick_sign;        // half-signed(1) / unsigned(0) configuration

	//-------------Outputs---------------------------------
	output        [3:0] p_22;

	//-------------Internal signals------------------------
	logic         [2:0] w;
	
	//-------------Datapath--------------------------------

	always_comb begin		
		w = (pick_sign) ? {w_22[1],w_22} : {1'b0,w_22};
	end	

	assign p_22 = $signed(w)*$signed({1'b0,a_22});


endmodule // BitBrick22_v2
//-------------------------------------------------------------
// Design:        BitBrick44_c1
// Description:   4x4 unit block for BitFusion @ colum 1
// Working config_aw:  config_aw 000 -> #1  8x8b -> (symmetric scaling)  + (column 3 Positive) + (column 2&4 Positive) 
//                config_aw 010 -> #4  4x4b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Positive) 
//                config_aw 011 -> #16 2x2b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Negative)
//                config_aw 110 -> #2  8x4b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Positive)
//                config_aw 111 -> #4  8x2b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Negative)             
// Author:	      Linyan Mei
//-------------------------------------------------------------

module BitBrick44_c1 (a_44_11, a_44_12, a_44_21, a_44_22,
					  w_44_11, w_44_12, w_44_21, w_44_22, 
					  config_aw, p_44);

//	parameter VERSION = "v2";

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [1:0] a_44_11, a_44_12, a_44_21, a_44_22;             // unsigned activation  
	input         [1:0] w_44_11, w_44_12, w_44_21, w_44_22;             // signed / unsigned weight
	//----Control in-----
	input         [2:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [7:0] p_44;

	//-------------Internal signals-----------------------
	logic         [3:0] pp11, pp12, pp21, pp22;       // partial products (@ row & colum)
	logic         [3+2:0] ex_pp11;                    // extended partial products (<<0, <<2)
	logic         [3+0:0] ex_pp12;                    // extended partial products (<<0)
	logic         [3+4:0] ex_pp21;                    // extended partial products (<<0, <<2, <<4)
	logic         [3+2:0] ex_pp22;                    // extended partial products (<<0, <<2)

	logic         [7:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	BitBrick22_v2  BB11 (
		// Inputs
		.a_22(a_44_11), .w_22(w_44_11), 
		.pick_sign(1'b1),
		// Outputs
		.p_22(pp11)
	);

	BitBrick22_v2  BB12 (
		// Inputs
		.a_22(a_44_12), .w_22(w_44_12), 
		.pick_sign(config_aw[0]),
		// Outputs
		.p_22(pp12)
	);

	BitBrick22_v2  BB21 (
		// Inputs
		.a_22(a_44_21), .w_22(w_44_21), 
		.pick_sign(1'b1),
		// Outputs
		.p_22(pp21)
	);

	BitBrick22_v2  BB22 (
		// Inputs
		.a_22(a_44_22), .w_22(w_44_22), 
		.pick_sign(config_aw[0]),
		// Outputs
		.p_22(pp22)
	);

	always_comb begin
		unique case (config_aw)
			3'b000: begin ex_pp11 = {pp11,2'b0};                     // partial product (@ row 1 & colum 1) right shifts 2 bits -> extended partial product
						  ex_pp12 = pp12;                            // partial product (@ row 1 & colum 2) right shifts 0 bits -> extended partial product
						  ex_pp21 = {pp21,4'b0};                     // partial product (@ row 2 & colum 1) right shifts 4 bits -> extended partial product
						  ex_pp22 = {pp22,2'b0};                     // partial product (@ row 2 & colum 2) right shifts 2 bits -> extended partial product

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b010: begin ex_pp11 = {pp11,2'b0}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21,4'b0};
						  ex_pp22 = {pp22,2'b0}; 

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b011: begin ex_pp11 = {pp11[3],pp11[3],pp11};           // don't shift, just extend with MSB
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21[3],pp21[3],pp21[3],pp21[3],pp21};
						  ex_pp22 = {pp22[3],pp22[3],pp22};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			3'b110: begin ex_pp11 = {pp11,2'b0}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21,4'b0};
						  ex_pp22 = {pp22,2'b0};

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b111: begin ex_pp11 = {pp11[3],pp11[3],pp11}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21[3],pp21[3],pp21,2'b0};
						  ex_pp22 = {pp22,2'b0};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end
		endcase

		
	end	


	assign p_44 = psum;

endmodule // BitBrick44_c1
//-------------------------------------------------------------
// Design:        BitBrick44_c2
// Description:   4x4 unit block for BitFusion @ colum 2
// Working config_aw:  config_aw 000 -> #1  8x8b -> (symmetric scaling)  + (column 3 Positive) + (column 2&4 Positive) 
//                config_aw 010 -> #4  4x4b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Positive) 
//                config_aw 011 -> #16 2x2b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Negative)
//                config_aw 110 -> #2  8x4b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Positive)
//                config_aw 111 -> #4  8x2b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Negative)             
// Author:	      Linyan Mei
//-------------------------------------------------------------

module BitBrick44_c2 (a_44_11, a_44_12, a_44_21, a_44_22,
					  w_44_11, w_44_12, w_44_21, w_44_22, 
					  config_aw, p_44);

//	parameter VERSION = "v2";

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [1:0] a_44_11, a_44_12, a_44_21, a_44_22;             // unsigned activation  
	input         [1:0] w_44_11, w_44_12, w_44_21, w_44_22;             // signed / unsigned weight
	//----Control in-----
	input         [2:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [7:0] p_44;

	//-------------Internal signals-----------------------
	logic         [3:0] pp11, pp12, pp21, pp22;       // partial products (@ row & colum)
	logic         [3+2:0] ex_pp11;                    // extended partial products (<<0, <<2)
	logic         [3+0:0] ex_pp12;                    // extended partial products (<<0)
	logic         [3+4:0] ex_pp21;                    // extended partial products (<<0, <<2, <<4)
	logic         [3+2:0] ex_pp22;                    // extended partial products (<<0, <<2)

	logic         [7:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	BitBrick22_v2  BB11 (
		// Inputs
		.a_22(a_44_11), .w_22(w_44_11), 
		.pick_sign(config_aw[1]),
		// Outputs
		.p_22(pp11)
	);

	BitBrick22_v2  BB12 (
		// Inputs
		.a_22(a_44_12), .w_22(w_44_12), 
		.pick_sign(config_aw[0]),
		// Outputs
		.p_22(pp12)
	);

	BitBrick22_v2  BB21 (
		// Inputs
		.a_22(a_44_21), .w_22(w_44_21), 
		.pick_sign(config_aw[1]),
		// Outputs
		.p_22(pp21)
	);

	BitBrick22_v2  BB22 (
		// Inputs
		.a_22(a_44_22), .w_22(w_44_22), 
		.pick_sign(config_aw[0]),
		// Outputs
		.p_22(pp22)
	);

	always_comb begin
		unique case (config_aw)
			3'b000: begin ex_pp11 = {pp11,2'b0};                     // partial product (@ row 1 & colum 1) right shifts 2 bits -> extended partial product
						  ex_pp12 = pp12;                            // partial product (@ row 1 & colum 2) right shifts 0 bits -> extended partial product
						  ex_pp21 = {pp21,4'b0};                     // partial product (@ row 2 & colum 1) right shifts 4 bits -> extended partial product
						  ex_pp22 = {pp22,2'b0};                     // partial product (@ row 2 & colum 2) right shifts 2 bits -> extended partial product

						  psum = $signed({1'b0,ex_pp11}) + $signed({1'b0,ex_pp12}) + $signed({1'b0,ex_pp21}) + $signed({1'b0,ex_pp22});
					end

			3'b010: begin ex_pp11 = {pp11,2'b0}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21,4'b0};
						  ex_pp22 = {pp22,2'b0}; 

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b011: begin ex_pp11 = {pp11[3],pp11[3],pp11};           // don't shift, just extend with MSB
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21[3],pp21[3],pp21[3],pp21[3],pp21};
						  ex_pp22 = {pp22[3],pp22[3],pp22};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			3'b110: begin ex_pp11 = {pp11,2'b0}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21,4'b0};
						  ex_pp22 = {pp22,2'b0};

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b111: begin ex_pp11 = {pp11[3],pp11[3],pp11}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {pp21[3],pp21[3],pp21,2'b00};
						  ex_pp22 = {pp22,2'b0};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end
		endcase

		
	end	


	assign p_44 = psum;

endmodule // BitBrick44_c2
//-------------------------------------------------------------
// Design:        BitBrick88
// Description:   8x8 unit block for BitFusion
// Working config_aw:  config_aw 000 -> #1  8x8b -> (symmetric scaling)  + (column 3 Positive) + (column 2&4 Positive) 
//                config_aw 010 -> #4  4x4b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Positive) 
//                config_aw 011 -> #16 2x2b -> (symmetric scaling)  + (column 3 Negative) + (column 2&4 Negative)
//                config_aw 110 -> #2  8x4b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Positive)
//                config_aw 111 -> #4  8x2b -> (asymmetric scaling) + (column 3 Negative) + (column 2&4 Negative)             
// Author:	      Linyan Mei
//-------------------------------------------------------------

module BitBrick88 (a_88_11, a_88_12, a_88_13, a_88_14,
				   a_88_21, a_88_22, a_88_23, a_88_24,
				   a_88_31, a_88_32, a_88_33, a_88_34,
				   a_88_41, a_88_42, a_88_43, a_88_44,

				   w_88_11, w_88_12, w_88_13, w_88_14,
				   w_88_21, w_88_22, w_88_23, w_88_24,
				   w_88_31, w_88_32, w_88_33, w_88_34,
				   w_88_41, w_88_42, w_88_43, w_88_44,

				   config_aw, p_88);


	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [1:0] a_88_11, a_88_12, a_88_13, a_88_14,
				        a_88_21, a_88_22, a_88_23, a_88_24,
				   	    a_88_31, a_88_32, a_88_33, a_88_34,
				   		a_88_41, a_88_42, a_88_43, a_88_44;           // unsigned activation  

	input         [1:0] w_88_11, w_88_12, w_88_13, w_88_14,
				   		w_88_21, w_88_22, w_88_23, w_88_24,
				   		w_88_31, w_88_32, w_88_33, w_88_34,
				   		w_88_41, w_88_42, w_88_43, w_88_44;          // signed / unsigned weight

	//----Control in-----
	input         [2:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [15:0] p_88;

	//-------------Internal signals-----------------------
	logic         [7:0] pp11, pp12, pp21, pp22;       // partial products (@ row & colum)
	logic         [7+4:0] ex_pp11;                    // extended partial products (<<0, <<4)
	logic         [7+0:0] ex_pp12;                    // extended partial products (<<0)
	logic         [7+8:0] ex_pp21;                    // extended partial products (<<0, <<4, <<8)
	logic         [7+4:0] ex_pp22;                    // extended partial products (<<0, <<4)

	logic         [15:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick44_c1 BB44_11 (
		// Inputs
    	.a_44_11(a_88_11), .a_44_12(a_88_12), .a_44_21(a_88_21), .a_44_22(a_88_22),
		.w_44_11(w_88_11), .w_44_12(w_88_12), .w_44_21(w_88_21), .w_44_22(w_88_22),
		.config_aw(config_aw),
		// Outputs
		.p_44(pp11)
    );

	BitBrick44_c2 BB44_12 (
		// Inputs
    	.a_44_11(a_88_13), .a_44_12(a_88_14), .a_44_21(a_88_23), .a_44_22(a_88_24),
		.w_44_11(w_88_13), .w_44_12(w_88_14), .w_44_21(w_88_23), .w_44_22(w_88_24),
		.config_aw(config_aw),
		// Outputs
		.p_44(pp12)
    );

	BitBrick44_c1 BB44_21 (
		// Inputs
    	.a_44_11(a_88_31), .a_44_12(a_88_32), .a_44_21(a_88_41), .a_44_22(a_88_42),
		.w_44_11(w_88_31), .w_44_12(w_88_32), .w_44_21(w_88_41), .w_44_22(w_88_42),
		.config_aw(config_aw),
		// Outputs
		.p_44(pp21)
    );

	BitBrick44_c2 BB44_22 (
		// Inputs
    	.a_44_11(a_88_33), .a_44_12(a_88_34), .a_44_21(a_88_43), .a_44_22(a_88_44),
		.w_44_11(w_88_33), .w_44_12(w_88_34), .w_44_21(w_88_43), .w_44_22(w_88_44),
		.config_aw(config_aw),
		// Outputs
		.p_44(pp22)
    );


	always_comb begin
		unique case (config_aw)
			3'b000: begin ex_pp11 = {pp11,4'b0};                     // partial product (@ row 1 & colum 1) right shifts 4 bits -> extended partial product
						  ex_pp12 = pp12;                            // partial product (@ row 1 & colum 2) right shifts 0 bits -> extended partial product
						  ex_pp21 = {pp21,8'b0};                     // partial product (@ row 2 & colum 1) right shifts 8 bits -> extended partial product
						  ex_pp22 = {pp22,4'b0};                     // partial product (@ row 2 & colum 2) right shifts 4 bits -> extended partial product

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			3'b010: begin ex_pp11 = {{4{pp11[7]}},pp11};               // don't shift, just extend with MSB
						  ex_pp12 = pp12;
						  ex_pp21 = {{8{pp21[7]}},pp21};
						  ex_pp22 = {{4{pp22[7]}},pp22}; 

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			3'b011: begin ex_pp11 = {{4{pp11[7]}},pp11};               // don't shift, just extend with MSB
						  ex_pp12 = pp12;
						  ex_pp21 = {{8{pp21[7]}},pp21};
						  ex_pp22 = {{4{pp22[7]}},pp22}; 

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			3'b110: begin ex_pp11 = {{4{pp11[7]}},pp11}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {{4{pp21[7]}},pp21,4'b0};
						  ex_pp22 = {pp22,4'b0};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			3'b111: begin ex_pp11 = {{4{pp11[7]}},pp11}; 
						  ex_pp12 = pp12;
						  ex_pp21 = {{4{pp21[7]}},pp21,4'b0};
						  ex_pp22 = {pp22,4'b0};

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end
		endcase

		
	end	


	assign p_88 = psum;

endmodule // BitBrick88
//-------------------------------------------------------------
// Design:        BitFusion_top
// Description:   BitFusion top level
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 000 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register
//                config_aw 010 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register
//                config_aw 011 -> #16 2x2b -> activate  8 bits /  8 bits + headroom register
//                config_aw 110 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register
//                config_aw 111 -> #4  8x2b -> activate 12 bits / 12 bits + headroom register
// Author:	      Linyan Mei
//-------------------------------------------------------------

module BitFusion_top (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------
	//----basic in--------
	input 		  clk, rst, accu_rst;

	//----Data in--------
	input         [3:0][3:0][1:0] a ;           // unsigned activation
	input         [3:0][3:0][1:0] w ;           // signed / unsigned weight

	//----Control in-----
	input         [2:0] config_aw;

	//-------------Outputs---------------------------------
	output   reg  [15+HEADROOM:0] z ;
	logic         [15+HEADROOM:0] z_tmp;

	//-------------Internal signals-----------------------
	reg			  [15:0] mult;
	logic         [15:0] mult_tmp, p_88;

	logic 		  [3:0]  gating;

	logic 		  clk3, clk2, clk1, clk0;
	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick88 BitBrick88 (
    .a_88_11(a[0][0]), .a_88_12(a[0][1]), .a_88_13(a[0][2]), .a_88_14(a[0][3]),
	.a_88_21(a[1][0]), .a_88_22(a[1][1]), .a_88_23(a[1][2]), .a_88_24(a[1][3]),
	.a_88_31(a[2][0]), .a_88_32(a[2][1]), .a_88_33(a[2][2]), .a_88_34(a[2][3]),
	.a_88_41(a[3][0]), .a_88_42(a[3][1]), .a_88_43(a[3][2]), .a_88_44(a[3][3]),

	.w_88_11(w[0][0]), .w_88_12(w[0][1]), .w_88_13(w[0][2]), .w_88_14(w[0][3]),
	.w_88_21(w[1][0]), .w_88_22(w[1][1]), .w_88_23(w[1][2]), .w_88_24(w[1][3]),
	.w_88_31(w[2][0]), .w_88_32(w[2][1]), .w_88_33(w[2][2]), .w_88_34(w[2][3]),
	.w_88_41(w[3][0]), .w_88_42(w[3][1]), .w_88_43(w[3][2]), .w_88_44(w[3][3]),
	.config_aw(config_aw),
	.p_88(p_88)
    );


	// clock gating signal generation
	always_comb begin
		unique case (config_aw)
			3'b000: gating = 4'b0000;

			3'b010: gating = 4'b1110;

			3'b011: gating = 4'b1111;

			3'b110: gating = 4'b1000;

			3'b111: gating = 4'b1100;
		endcase
	end

	always_comb begin
		clk3 = clk & ~gating[3];
		clk2 = clk & ~gating[2];
		clk1 = clk & ~gating[1];
		clk0 = clk & ~gating[0];
	end

	// flip-flops never clock-gated
	always_ff @(posedge clk) begin
		if (rst) begin
			z    [7+HEADROOM:0]  <= 0;
			mult [7         :0]  <= 0;
		end
		else begin
			z    [7+HEADROOM:0]  <= z_tmp    [7+HEADROOM:0];
			mult [7         :0]  <= mult_tmp [7         :0];
		end
	end

	// clock-gated flip-flops ---------------------------------------
	always_ff @(posedge clk3) begin
		if (rst) begin
			z    [15+HEADROOM:13+HEADROOM]  <= 0;
			mult [15         :13         ]  <= 0;
		end
		else begin
			z    [15+HEADROOM:13+HEADROOM]  <= z_tmp    [15+HEADROOM:13+HEADROOM];
			mult [15         :13         ]  <= mult_tmp [15         :13         ];
		end
	end

	always_ff @(posedge clk2) begin
		if (rst) begin
			z    [12+HEADROOM]  <= 0;
			mult [12         ]  <= 0;
		end
		else begin
			z    [12+HEADROOM]  <= z_tmp    [12+HEADROOM];
			mult [12         ]  <= mult_tmp [12         ];
		end
	end

	always_ff @(posedge clk1) begin
		if (rst) begin
			z    [11+HEADROOM:10+HEADROOM]  <= 0;
			mult [11         :10         ]  <= 0;
		end
		else begin
			z    [11+HEADROOM:10+HEADROOM]  <= z_tmp    [11+HEADROOM:10+HEADROOM];
			mult [11         :10         ]  <= mult_tmp [11         :10         ];
		end
	end

	always_ff @(posedge clk0) begin
		if (rst) begin
			z    [9+HEADROOM:8+HEADROOM]  <= 0;
			mult [9         :8         ]  <= 0;
		end
		else begin
			z    [9+HEADROOM:8+HEADROOM]  <= z_tmp    [9+HEADROOM:8+HEADROOM];
			mult [9         :8         ]  <= mult_tmp [9         :8         ];
		end
	end
	//---------------------------------------------------------------

	// logic
	always_comb begin
		unique case (config_aw)
			3'b000: z_tmp    = (accu_rst) ? '0 : $signed(z) + $signed({{HEADROOM{mult[15]}},mult});

			3'b010: z_tmp    = (accu_rst) ? '0 : $signed(z[9+HEADROOM:0]) + $signed({{HEADROOM{mult[9]}},mult[9:0]});

			3'b011: z_tmp    = (accu_rst) ? '0 : $signed(z[7+HEADROOM:0]) + $signed({{HEADROOM{mult[7]}},mult[7:0]});

			3'b110: z_tmp    = (accu_rst) ? '0 : $signed(z[12+HEADROOM:0]) + $signed({{HEADROOM{mult[12]}},mult[12:0]});

			3'b111: z_tmp    = (accu_rst) ? '0 : $signed(z[11+HEADROOM:0]) + $signed({{HEADROOM{mult[11]}},mult[11:0]});
		endcase
		mult_tmp = p_88;
	end




endmodule // BitFusion_top

