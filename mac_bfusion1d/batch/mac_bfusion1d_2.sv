//-------------------------------------------------------------
// Design:        bfusion1D_2_level MAC wrap with input register
// Description:   1D 2-level BitFusion MAC unit
// Version:       1.0
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 00 -> #1  8x8b
//                mode 01 -> #2  8x4b
//                mode 11 -> #4  8x2b
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
	input         [31:0]          a;           // unsigned activation 
	input         [ 7:0]          w;           // signed / unsigned weight 

	//----Control in-----
	input          [1:0]          mode;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	reg                           rst_reg;
	reg                           accu_rst_reg;

	reg           [31:0]          a_reg;
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
// Design:        1D bfusion_2_level MAC wrap without input register
// Description:   1D 2-level BitFusion MAC unit
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 00 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                mode 01 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register 
//                mode 11 -> #4  8x2b -> activate 12 bits / 12 bits + headroom register     
// Author:	      Linyan Mei
//-------------------------------------------------------------

module mac_bfusion1d (clk, rst, accu_rst, a, w, mode, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------	
	//----basic in--------
	input 				 clk, rst, accu_rst;

	//----Data in--------
	input         [31:0] a ;           // unsigned activation 
	input         [ 7:0] w ;           // signed / unsigned weight 

	//----Control in-----
	input         [1:0] mode;             

	//-------------Outputs---------------------------------
	output        [15+HEADROOM:0] z;
	
	//-------------Internal signals-----------------------
	logic        [3:0][7:0] a_wrap;  // signed
	logic        [3:0][1:0] w_wrap;  // unsigned



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
			2'b00: begin 
						a_wrap = {{a[7:0],a[7:0]},
							      {a[7:0],a[7:0]}};

						w_wrap = {{w[7:6],w[5:4]},
							      {w[3:2],w[1:0]}};
					end

			// 84
			2'b01: begin 
						a_wrap = {{a[15:8],a[15:8]},
							      {a[ 7:0],a[ 7:0]}};

						w_wrap = {{w[7:6],w[5:4]},
							      {w[3:2],w[1:0]}};
					end

			// 82
			2'b11: begin 
						a_wrap = {{a[31:24],a[23:16]},
							      {a[15: 8],a[ 7: 0]}};

						w_wrap = {{w[7:6],w[5:4]},
							      {w[3:2],w[1:0]}};
					end
		endcase
	end	

endmodule // bfusion1D_2_level



//-------------------------------------------------------------
// Design:        BitFusion
// Description:   1D BitFusion with output register
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 00 -> #1  8x8b
//                mode 01 -> #2  8x4b
//                mode 11 -> #4  8x2b
//-------------------------------------------------------------

module BitFusion (clk, rst, accu_rst, a, w, mode, z);

	parameter HEADROOM = 4;

	//-------------Inputs----------------------------------
	//----basic in--------
	input 		  clk, rst, accu_rst;

	//----Data in--------
	input         [3:0][7:0] a ;           // unsigned activation
	input         [3:0][1:0] w ;           // signed / unsigned weight

	//----Control in-----
	input              [1:0] mode;

	//-------------Outputs---------------------------------
	output   reg  [15+HEADROOM:0] z ;
	logic         [15+HEADROOM:0] z_tmp;

	//-------------Internal signals-----------------------
	reg			  [15:0] mult;
	logic         [15:0] mult_tmp, p_88;

	logic 		         clk1, clk0;
	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick88 BitBrick88 (
    .a_88_1(a[3]), .a_88_2(a[2]),
	.a_88_3(a[1]), .a_88_4(a[0]),

	.w_88_1(w[3]), .w_88_2(w[2]),
	.w_88_3(w[1]), .w_88_4(w[0]),

	.mode(mode),
	.p_88(p_88)
    );


	// clock gating signal generation
	always_comb begin
		clk1 = (clk & ~mode[0]) | (clk & rst);
		clk0 = (clk & ~mode[1]) | (clk & rst);
	end

	// flip-flops never clock-gated
	always_ff @(posedge clk) begin
		if (rst) begin
			z    [11+HEADROOM:0]  <= 0;
			mult [11         :0]  <= 0;
		end
		else begin
			z    [11+HEADROOM:0]  <= z_tmp    [11+HEADROOM:0];
			mult [11         :0]  <= mult_tmp [11         :0];
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

	always_ff @(posedge clk0) begin
		if (rst) begin
			z    [12+HEADROOM            ]  <= 0;
			mult [12                     ]  <= 0;
		end
		else begin
			z    [12+HEADROOM            ]  <= z_tmp    [12+HEADROOM            ];
			mult [12                     ]  <= mult_tmp [12                     ];
		end
	end

	//---------------------------------------------------------------

	// logic
	always_comb begin
		unique case (mode)
			2'b00: z_tmp    = (accu_rst) ? '0 : $signed(z) + $signed({{HEADROOM{mult[15]}},mult});

			2'b01: z_tmp    = (accu_rst) ? '0 : $signed(z[12+HEADROOM:0]) + $signed({{HEADROOM{mult[12]}},mult[12:0]});

			2'b11: z_tmp    = (accu_rst) ? '0 : $signed(z[11+HEADROOM:0]) + $signed({{HEADROOM{mult[11]}},mult[11:0]});
		endcase
		mult_tmp = p_88;
	end

endmodule // BitFusion



//-------------------------------------------------------------
// Design:        BitBrick88
// Description:   8x8 unit block for 2-level 1D-BitFusion
// Working mode:  mode 00 -> #1  8x8b -> (Block 1 Negative)      + (Block 2,3,4 Positive) 
//                mode 01 -> #2  8x4b -> (Block 1,3 Negative)    + (Block 2,4 Positive) 
//                mode 11 -> #4  8x2b -> (Block 1,2,3,4 Negative)           
//-------------------------------------------------------------

module BitBrick88 (a_88_1, a_88_2,
				   a_88_3, a_88_4,

				   w_88_1, w_88_2,
				   w_88_3, w_88_4,

				   mode, p_88);


	//-------------Inputs----------------------------------	
	//----Data in--------
	input            [7:0] a_88_1, a_88_2,
				           a_88_3, a_88_4;        // unsigned activation  

	input            [1:0] w_88_1, w_88_2,
				           w_88_3, w_88_4;        // signed / unsigned weight

	//----Control in-----
	input            [1:0] mode;             

	//-------------Outputs---------------------------------
	output          [15:0] p_88;

	//-------------Internal signals-----------------------

	logic           [11:0] pp1, pp2;            // partial products (from left to right)
	logic         [11+4:0] ex_pp1;              // extended partial products (<<0, <<4)
	logic         [11+0:0] ex_pp2;              // extended partial products (<<0)

	logic           [15:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------

	BitBrick84_left BB84_left (
		// Inputs
    	.a_84_1(a_88_1), .a_84_2(a_88_2),
		.w_84_1(w_88_1), .w_84_2(w_88_2),
		.mode(mode),
		// Outputs
		.p_84(pp1)
    );

	BitBrick84_right BB84_right (
		// Inputs
    	.a_84_1(a_88_3), .a_84_2(a_88_4),
		.w_84_1(w_88_3), .w_84_2(w_88_4),
		.mode(mode),
		// Outputs
		.p_84(pp2)
    );


	// generate sum from shifted partial products
	always_comb begin
		unique case (mode)
			// A8,W8
			2'b00: begin  ex_pp1 = {pp1,4'b0};
						  ex_pp2 = pp2;

						  psum = $signed(ex_pp1) + $signed({1'b0,ex_pp2});
					end

			// A8,W4
			2'b01: begin  ex_pp1 = {{4{pp1[11]}},pp1};            
						  ex_pp2 = pp2;

						  psum = $signed(ex_pp1) + $signed(ex_pp2);
					end

			// A8,W2
			2'b11: begin  ex_pp1 = {{4{pp1[11]}},pp1}; 
						  ex_pp2 = pp2;

						  psum = $signed(ex_pp1) + $signed(ex_pp2);
					end
		endcase	
	end	


	assign p_88 = psum;

endmodule // BitBrick88



//-------------------------------------------------------------
// Design:        BitBrick84_left
// Description:   8x4 unit block for 2-level 1D-BitFusion (left one)
// Working mode:  mode 00 -> #1  8x8b
//                mode 01 -> #2  8x4b
//                mode 11 -> #4  8x2b
//-------------------------------------------------------------

module BitBrick84_left (a_84_1, a_84_2,
				        w_84_1, w_84_2, 
				        mode, p_84);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [7:0] a_84_1, a_84_2;             // unsigned activation  
	input         [1:0] w_84_1, w_84_2;             // signed / unsigned weight
	//----Control in-----
	input         [1:0] mode;             

	//-------------Outputs---------------------------------
	output        [11:0] p_84;

	//-------------Internal signals-----------------------
	logic         [9:0] pp1, pp2;                   // partial products
	logic         [9+2:0] ex_pp1;                   // extended partial products (<<0, <<2)
	logic         [9+0:0] ex_pp2;                   // extended partial products (<<0)

	logic         [11:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	BitBrick82  BB1 (
		// Inputs
		.a_8b(a_84_1), .w_2b(w_84_1), 
		.pick_sign(1'b1),
		// Outputs
		.p_82(pp1)
	);

	BitBrick82  BB2 (
		// Inputs
		.a_8b(a_84_2), .w_2b(w_84_2), 
		.pick_sign(mode[1]),
		// Outputs
		.p_82(pp2)
	);


	always_comb begin
		unique case (mode)
			2'b00: begin  ex_pp1 = {pp1,2'b0};                     // partial product (@ position 1) left shifts 2 bits -> extended partial product
						  ex_pp2 = pp2;                            // partial product (@ position 2) left shifts 0 bits -> extended partial product

						  psum = $signed(ex_pp1) + $signed({1'b0,ex_pp2});
					end

			2'b01: begin  ex_pp1 = {pp1,2'b0};            
						  ex_pp2 = pp2;                   

						  psum = $signed(ex_pp1) + $signed({1'b0,ex_pp2});
					end

			2'b11: begin  ex_pp1 = {{2{pp1[9]}},pp1};            
						  ex_pp2 = pp2;                   

						  psum = $signed(ex_pp1) + $signed(ex_pp2);
					end
		endcase

		
	end	

	assign p_84 = psum;

endmodule // BitBrick84_left





//-------------------------------------------------------------
// Design:        BitBrick84_right
// Description:   8x4 unit block for 2-level 1D-BitFusion (left one)
// Working mode:  mode 00 -> #1  8x8b
//                mode 01 -> #2  8x4b
//                mode 11 -> #4  8x2b
//-------------------------------------------------------------

module BitBrick84_right (a_84_1, a_84_2,
				        w_84_1, w_84_2, 
				        mode, p_84);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [7:0] a_84_1, a_84_2;             // unsigned activation  
	input         [1:0] w_84_1, w_84_2;             // signed / unsigned weight
	//----Control in-----
	input         [1:0] mode;             

	//-------------Outputs---------------------------------
	output        [11:0] p_84;

	//-------------Internal signals-----------------------
	logic         [9:0] pp1, pp2;                   // partial products
	logic         [9+2:0] ex_pp1;                   // extended partial products (<<0, <<2)
	logic         [9+0:0] ex_pp2;                   // extended partial products (<<0)

	logic         [11:0] psum;	

	//-------------Datapath--------------------------------

	//-------------UUT instantiation----------
	BitBrick82  BB3 (
		// Inputs
		.a_8b(a_84_1), .w_2b(w_84_1), 
		.pick_sign(mode[0]),
		// Outputs
		.p_82(pp1)
	);

	BitBrick82  BB4 (
		// Inputs
		.a_8b(a_84_2), .w_2b(w_84_2), 
		.pick_sign(mode[1]),
		// Outputs
		.p_82(pp2)
	);


	always_comb begin
		unique case (mode)
			2'b00: begin  ex_pp1 = {pp1,2'b0};                     // partial product (@ position 1) left shifts 2 bits -> extended partial product
						  ex_pp2 = pp2;                            // partial product (@ position 2) left shifts 0 bits -> extended partial product

						  psum = $signed({1'b0,ex_pp1}) + $signed({1'b0,ex_pp2});
					end

			2'b01: begin  ex_pp1 = {pp1,2'b0};            
						  ex_pp2 = pp2;                   

						  psum = $signed(ex_pp1) + $signed({1'b0,ex_pp2});
					end

			2'b11: begin  ex_pp1 = {{2{pp1[9]}},pp1};            
						  ex_pp2 = pp2;                   

						  psum = $signed(ex_pp1) + $signed(ex_pp2);
					end
		endcase

		
	end	

	assign p_84 = psum;

endmodule // BitBrick84_right



//-------------------------------------------------------------
// Design:        BitBrick82
// Description:   8x2 unit block for 2-level 1D-BitFusion
// Working mode:  Half-signed / Unsigned multiplication
//-------------------------------------------------------------

module BitBrick82 (a_8b, w_2b, pick_sign, p_82);

	//-------------Inputs----------------------------------	
	//----Data in--------
	input         [7:0] a_8b;             // unsigned activation  
	input         [1:0] w_2b;             // signed / unsigned weight
	//----Control in-----
	input               pick_sign;        // half-signed(1) / unsigned(0) configuration

	//-------------Outputs---------------------------------
	output        [9:0] p_82;

	//-------------Internal signals------------------------
	logic         [2:0] w;
	
	//-------------Datapath--------------------------------

	always_comb begin		
		w = (pick_sign) ? {w_2b[1],w_2b} : {1'b0,w_2b};
	end	

	assign p_82 = $signed(w)*$signed({1'b0,a_8b});

endmodule // BitBrick82

