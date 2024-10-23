//-------------------------------------------------------------
// Design:        mac_bfusion MAC wrap with input register
// Description:   1-level BitFusion MAC unit
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 00 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                config_aw 01 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register 
//                config_aw 11 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register     
// Author:	      Linyan Mei
//-------------------------------------------------------------

module top_mac_bfusion (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				          clk;
	input 				          rst;
	input 				          accu_rst;

	//----Data in--------
	input         [15:0]          a;           // unsigned activation 
	input         [15:0]          w;           // signed / unsigned weight 

	//----Control in-----
	input          [1:0]          config_aw;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	reg                           rst_reg;
	reg                           accu_rst_reg;

	reg           [15:0]          a_reg;
	reg           [15:0]          w_reg;



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


endmodule // top_mac_bfusion


//-------------------------------------------------------------
// Design:        mac_bfusion MAC wrap without input register
// Description:   1-level BitFusion MAC unit
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 00 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                config_aw 01 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register 
//                config_aw 11 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register     
// Author:	      Linyan Mei
//-------------------------------------------------------------

module mac_bfusion (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				clk, rst, accu_rst;

	//----Data in--------
	input         [15:0] a ;           // unsigned activation 
	input         [15:0] w ;           // signed / unsigned weight 

	//----Control in-----
	input         [1:0] config_aw;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	logic        [1:0][1:0][3:0] a_wrap;  // signed
	logic        [1:0][1:0][3:0] w_wrap;  // unsigned



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
		.config_aw       (config_aw),
		// Outputs
		.z          (z)
	);


	//---------data rearrangement and dispatch--------
	always_comb begin
		unique case (config_aw)
			2'b00: begin 
						a_wrap = {{a[7:4],a[7:4]},
							      {a[3:0],a[3:0]}};

						w_wrap = {{w[3:0],w[7:4]},
							      {w[3:0],w[7:4]}};
					end

			2'b01: begin 
						a_wrap = {{a[15:12],a[7:4]},
							      {a[11: 8],a[3:0]}};

						w_wrap = {{w[15:12],w[7:4]},
							      {w[11: 8],w[3:0]}};
					end

			2'b11: begin 
						a_wrap = {{a[15:12],a[7:4]},
							      {a[11: 8],a[3:0]}};

						w_wrap = {{w[7:4],w[3:0]},
							      {w[7:4],w[3:0]}};
					end
		endcase
	end	

endmodule // mac_bfusion



//-------------------------------------------------------------
// Design:        BitFusion
// Description:   BitFusion with output register
// Working config_aw:  Always do half-signed multiplication (unsigned activation * signed weight)
//                config_aw 00 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register
//                config_aw 01 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register
//                config_aw 11 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register
//-------------------------------------------------------------

module BitFusion (clk, rst, accu_rst, a, w, config_aw, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------
	//----basic in--------
	input 		  clk, rst, accu_rst;

	//----Data in--------
	input         [1:0][1:0][3:0] a ;           // unsigned activation
	input         [1:0][1:0][3:0] w ;           // signed / unsigned weight

	//----Control in-----
	input         [1:0] config_aw;

	//-------------Outputs---------------------------------
	output   reg  [15+HEADROOM:0] z ;
	logic         [15+HEADROOM:0] z_tmp;

	//-------------Internal signals-----------------------
	reg			  [15:0] mult;
	logic         [15:0] mult_tmp, p_88;

	logic 		  [2:0]  gating;

	logic 		         clk2, clk1, clk0;
	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick88 BitBrick88 (
    .a_88_11(a[0][0]), .a_88_12(a[0][1]),
	.a_88_21(a[1][0]), .a_88_22(a[1][1]),

	.w_88_11(w[0][0]), .w_88_12(w[0][1]),
	.w_88_21(w[1][0]), .w_88_22(w[1][1]),

	.config_aw(config_aw),
	.p_88(p_88)
    );


	// clock gating signal generation
	always_comb begin
		unique case (config_aw)
			2'b00: gating = 3'b000;

			2'b01: gating = 3'b111;

			2'b11: gating = 3'b100;
		endcase
	end

	always_comb begin
		clk2 = (clk & ~gating[2]) | (clk & rst);
		clk1 = (clk & ~gating[1]) | (clk & rst);
		clk0 = (clk & ~gating[0]) | (clk & rst);
	end

	// flip-flops never clock-gated
	always_ff @(posedge clk) begin
		if (rst) begin
			z    [9+HEADROOM:0]  <= 0;
			mult [9         :0]  <= 0;
		end
		else begin
			z    [9+HEADROOM:0]  <= z_tmp    [9+HEADROOM:0];
			mult [9         :0]  <= mult_tmp [9         :0];
		end
	end

	// clock-gated flip-flops ---------------------------------------
	always_ff @(posedge clk2) begin
		if (rst) begin
			z    [15+HEADROOM:13+HEADROOM]  <= 0;
			mult [15         :13         ]  <= 0;
		end
		else begin
			z    [15+HEADROOM:13+HEADROOM]  <= z_tmp    [15+HEADROOM:13+HEADROOM];
			mult [15         :13         ]  <= mult_tmp [15         :13         ];
		end
	end

	always_ff @(posedge clk1) begin
		if (rst) begin
			z    [12+HEADROOM]  <= 0;
			mult [12         ]  <= 0;
		end
		else begin
			z    [12+HEADROOM]  <= z_tmp    [12+HEADROOM];
			mult [12         ]  <= mult_tmp [12         ];
		end
	end

	always_ff @(posedge clk0) begin
		if (rst) begin
			z    [11+HEADROOM:10+HEADROOM]  <= 0;
			mult [11         :10         ]  <= 0;
		end
		else begin
			z    [11+HEADROOM:10+HEADROOM]  <= z_tmp    [11+HEADROOM:10+HEADROOM];
			mult [11         :10         ]  <= mult_tmp [11         :10         ];
		end
	end

	//---------------------------------------------------------------

	// logic
	always_comb begin
		unique case (config_aw)
			2'b00: z_tmp    = (accu_rst) ? '0 : $signed(z) + $signed({{HEADROOM{mult[15]}},mult});

			2'b01: z_tmp    = (accu_rst) ? '0 : $signed(z[9+HEADROOM:0]) + $signed({{HEADROOM{mult[9]}},mult[9:0]});

			2'b11: z_tmp    = (accu_rst) ? '0 : $signed(z[12+HEADROOM:0]) + $signed({{HEADROOM{mult[12]}},mult[12:0]});
		endcase
		mult_tmp = p_88;
	end

endmodule // BitFusion





//-------------------------------------------------------------
// Design:        BitBrick88
// Description:   8x8 unit block for 1-level BitFusion
// Working config_aw:  config_aw 00 -> #1  8x8b -> (symmetric scaling)  + (column 1 Negative) + (column 2 Positive) 
//                config_aw 01 -> #4  4x4b -> (symmetric scaling)  + (column 1 Negative) + (column 2 Negative) 
//                config_aw 11 -> #2  8x4b -> (asymmetric scaling) + (column 1 Negative) + (column 2 Negative)            
//-------------------------------------------------------------

module BitBrick88 (a_88_11, a_88_12,
				   a_88_21, a_88_22,

				   w_88_11, w_88_12,
				   w_88_21, w_88_22,

				   config_aw, p_88);


	//-------------Inputs----------------------------------	
	//----Data in--------
	input          [3:0] a_88_11, a_88_12,
				         a_88_21, a_88_22;        // unsigned activation  

	input          [3:0] w_88_11, w_88_12,
				    	 w_88_21, w_88_22;        // signed / unsigned weight

	//----Control in-----
	input          [1:0] config_aw;             

	//-------------Outputs---------------------------------
	output         [15:0] p_88;

	//-------------Internal signals-----------------------
	logic                 pick_sign11, pick_sign12, pick_sign21, pick_sign22;

	logic           [7:0] pp11, pp12, pp21, pp22;     // partial products (@ row & colum)
	logic         [7+4:0] ex_pp11;                    // extended partial products (<<0, <<4)
	logic         [7+0:0] ex_pp12;                    // extended partial products (<<0)
	logic         [7+8:0] ex_pp21;                    // extended partial products (<<0, <<4, <<8)
	logic         [7+4:0] ex_pp22;                    // extended partial products (<<0, <<4)

	logic         [15:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick44 BB44_11 (
		// Inputs
    	.a_4b(a_88_11),
		.w_4b(w_88_11),
		.pick_sign(pick_sign11),
		// Outputs
		.p_44(pp11)
    );

	BitBrick44 BB44_12 (
		// Inputs
    	.a_4b(a_88_12),
		.w_4b(w_88_12),
		.pick_sign(pick_sign12),
		// Outputs
		.p_44(pp12)
    );

	BitBrick44 BB44_21 (
		// Inputs
    	.a_4b(a_88_21),
		.w_4b(w_88_21),
		.pick_sign(pick_sign21),
		// Outputs
		.p_44(pp21)
    );

	BitBrick44 BB44_22 (
		// Inputs
    	.a_4b(a_88_22),
		.w_4b(w_88_22),
		.pick_sign(pick_sign22),
		// Outputs
		.p_44(pp22)
    );


	always_comb begin
		unique case (config_aw)
			// A8,W8
			2'b00: begin 
						pick_sign11 = 1'b1;
						pick_sign12 = 1'b0;
						pick_sign21 = 1'b1;
						pick_sign22 = 1'b0;
					end

			// A4,W4
			2'b01: begin  
						pick_sign11 = 1'b1;
						pick_sign12 = 1'b1;
						pick_sign21 = 1'b1;
						pick_sign22 = 1'b1;
					end

			// A8,W4
			2'b11: begin 
						pick_sign11 = 1'b1;
						pick_sign12 = 1'b1;
						pick_sign21 = 1'b1;
						pick_sign22 = 1'b1;
					end
		endcase	
	end	


	// generate sum from shifted partial products
	always_comb begin
		unique case (config_aw)
			// A8,W8
			2'b00: begin  ex_pp11 = {pp11,4'b0};                     // partial product (@ row 1 & colum 1) right shifts 4 bits -> extended partial product
						  ex_pp12 = pp12;                            // partial product (@ row 1 & colum 2) right shifts 0 bits -> extended partial product
						  ex_pp21 = {pp21,8'b0};                     // partial product (@ row 2 & colum 1) right shifts 8 bits -> extended partial product
						  ex_pp22 = {pp22,4'b0};                     // partial product (@ row 2 & colum 2) right shifts 4 bits -> extended partial product

						  psum = $signed(ex_pp11) + $signed({1'b0,ex_pp12}) + $signed(ex_pp21) + $signed({1'b0,ex_pp22});
					end

			// A4,W4
			2'b01: begin  ex_pp11 = {{4{pp11[7]}},pp11};               // don't shift, just extend with MSB
						  ex_pp12 = pp12;
						  ex_pp21 = {{8{pp21[7]}},pp21};
						  ex_pp22 = {{4{pp22[7]}},pp22}; 

						  psum = $signed(ex_pp11) + $signed(ex_pp12) + $signed(ex_pp21) + $signed(ex_pp22);
					end

			// A8,W4
			2'b11: begin  ex_pp11 = {{4{pp11[7]}},pp11}; 
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
// Design:        BitBrick44
// Description:   4x4 unit block for 1-level BitFusion
// Working config_aw:  Half-signed / Unsigned multiplication
//-------------------------------------------------------------

module BitBrick44 (a_4b, w_4b, pick_sign, p_44);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [3:0] a_4b;             // unsigned activation  
	input         [3:0] w_4b;             // could be signed / unsigned weight
	//----Control in-----
	input               pick_sign;        // half-signed(1) / unsigned(0) configuration

	//-------------Outputs---------------------------------
	output        [7:0] p_44;

	//-------------Internal signals------------------------
	logic         [4:0] w;
	
	//-------------Datapath--------------------------------

	always_comb begin		
		w = (pick_sign) ? {w_4b[3],w_4b} : {1'b0,w_4b};
	end	

	assign p_44 = $signed(w)*$signed({1'b0,a_4b});


endmodule // BitBrick44


