//-------------------------------------------------------------
// Design:        testbench for 2D single bit-serial MAC 
// Description:   2D bit-serial MAC unit from Loom
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0000 -> 8(A)x8(W)b
//                mode 0111 -> 4(A)x4(W)b
//                mode 1111 -> 2(A)x2(W)b
//                mode 0001 -> 8(A)x4(W)b
//                mode 0011 -> 8(A)x2(W)b       
// Author:	      Vincent Camus, Linyan Mei
//-------------------------------------------------------------

`timescale 1ns/100fs

module pb_mac_serial2d;

	//-------------Testbench parameter---------------------
	parameter  W_CHOSEN_WIDTH;
	parameter  A_CHOSEN_WIDTH;
	parameter  VCD_FILE;
	parameter  STIMULI_MAX;
	parameter  CLK_PERIOD;
	parameter  STIMULI_FILE;
	
	//-------------Design parameter------------------------
	parameter  HEADROOM = 4;
	parameter  N_WIDTH  = 1;
	
	//-------------Local testbench parameters--------------
	localparam W_ACTIVE_WIDTH  = 2**($clog2(W_CHOSEN_WIDTH)) > N_WIDTH
		? 2**($clog2(W_CHOSEN_WIDTH)) : N_WIDTH;
	localparam A_ACTIVE_WIDTH  = 2**($clog2(A_CHOSEN_WIDTH)) > N_WIDTH
		? 2**($clog2(A_CHOSEN_WIDTH)) : N_WIDTH;

	//-------------UUT signals-----------------------------
	
	// basic
	logic                       clk_fast          = 0;
	logic                       clk_slow          = 0;
	logic                       rst               = 0;
	logic                       rst_mult          = 0;
	logic                       rst_mult_delayed = '0;

	// config
	logic                 [3:0] mode         = 4'b0000;
	
	// MAC FSM
	logic                       shift_ctr    = 0;
	logic                       sign_ctr     = 0;
	logic                 [2:0] w_sel        = 0;
	logic                 [2:0] a_sel        = 0;

	// operands
	logic                 [7:0] w_o          = 0;       // signed
	logic                 [7:0] a_o          = 0;       // unsigned
	logic                 [7:0] w            = 0;       // signed
	logic                 [7:0] a            = 0;       // unsigned
	
	// outputs
	logic                [19:0] z;           // signed
	
	//-------------Bench signals---------------------------
	integer                     m;           // precision of activation
    integer                     n;           // precision of weight
	integer                     i_minus_j;

	logic                [19:0] z_exp;
	
	logic  [W_CHOSEN_WIDTH-1:0] w_line;
	logic  [A_CHOSEN_WIDTH-1:0] a_line;
	
	// files
	integer                     stimuli_fp;
	integer                     stimuli_nb;  // stimuli counter
	integer                     status;
	
	//-------------UUT instantiation-----------------------
	
	top_mac_serial2d #(
		// Parameters

	) top_mac_serial2d (
		// Inputs
		.clk_fast    (clk_fast),
		.clk_slow    (clk_slow),
		.rst         (rst), 
		.rst_mult    (rst_mult_delayed), 
		.mode        (mode), 
		.shift_ctr   (shift_ctr), 
		.sign_ctr    (sign_ctr),
		.w_sel       (w_sel),
		.a_sel       (a_sel), 
		.w           (w),
		.a           (a),
		// Outputs 
		.z           (z));


	//-------------Clock-----------------------------------
	initial clk_fast = 0;
  	always
      #(CLK_PERIOD/2) clk_fast = ~clk_fast;

	//-------------Secondary clock-------------------------	
	initial rst_mult_delayed = 0;
	always rst_mult_delayed = #(0.5*CLK_PERIOD) rst_mult;
	
	always_comb begin
		if (rst) begin
			clk_slow <= clk_fast;
		end
		else begin
			clk_slow <= #(CLK_PERIOD) rst_mult_delayed & clk_fast;
		end
	end
	
	//-----------------------------------------------------

	always_comb begin
		unique case (mode)
			4'b0000: begin m <= 8; n <= 8; end
			4'b0111: begin m <= 4; n <= 4; end
			4'b1111: begin m <= 2; n <= 2; end
			4'b0001: begin m <= 8; n <= 4; end
			4'b0011: begin m <= 8; n <= 2; end
		endcase
	end

	function int max;
		input int a;
		input int b;
		begin
			max = (a>b)? a:b;
		end	
	endfunction

	function int min;
		input int a;
		input int b;
		begin
			min = (a<b)? a:b;
		end	
	endfunction
	
	//-----------expected------------
	always @(posedge clk_slow) begin

		if (rst) begin
			z_exp <= 0;
		end
		else begin
			case (mode)
				4'b0000: z_exp <= #(1*CLK_PERIOD) $signed(z_exp) + ($signed({1'b0,a     })*$signed(w)           );
				4'b0111: z_exp <= #(1*CLK_PERIOD) $signed(z_exp) + ($signed({1'b0,a[3:0]})*$signed(w[3:0]) << 8 );
				4'b1111: z_exp <= #(1*CLK_PERIOD) $signed(z_exp) + ($signed({1'b0,a[1:0]})*$signed(w[1:0]) << 12);
				4'b0001: z_exp <= #(1*CLK_PERIOD) $signed(z_exp) + ($signed({1'b0,a     })*$signed(w[3:0]) << 4 );
				4'b0011: z_exp <= #(1*CLK_PERIOD) $signed(z_exp) + ($signed({1'b0,a     })*$signed(w[1:0]) << 6 );
			endcase
		end

	end
	
	property accumulation;
		(!rst)
		// $display("time=%-8d, a=%d, w=%d, z=%d, z_exp=%d, Yes? %b", $time, $unsigned(a_line), $signed(w_line), $signed(z), $signed(z_exp), (z==z_exp))
		|-> (z_exp == z)
	endproperty
	always @(negedge clk_slow) assert property (accumulation);
	
	//-----------testing------------
	
	initial begin

		// print
		$display("** Info: starting w%0d_a%0d_%1.3f in w%0d_a%0d active mode with %0d stimuli.",
			W_CHOSEN_WIDTH, A_CHOSEN_WIDTH, CLK_PERIOD, W_ACTIVE_WIDTH, A_ACTIVE_WIDTH, STIMULI_MAX);
		
		// open stimuli file
		stimuli_fp = $fopen(STIMULI_FILE, "r");
		stimuli_nb = 0;
		
		// Pre-configuration reset
		mode      = 4'b0000;
		rst       = 1;
		rst_mult  = 1;
		w            = 0;
		a            = 0;
		sign_ctr     = 0;
		shift_ctr    = 0;
		repeat (5) @(negedge clk_fast);
	
		//****************************************************************************************************************************************
		
		// choose configuration and continue reset
		if      ((W_ACTIVE_WIDTH == 8) && (A_ACTIVE_WIDTH == 8)) mode <= 4'b0000;
		else if ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 4)) mode <= 4'b0111;
		else if ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 2)) mode <= 4'b1111;
		else if ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 8)) mode <= 4'b0001;
		else if ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 8)) mode <= 4'b0011;
		else mode <= 4'bxxxx;
		repeat (5) @(negedge clk_fast);
		
		$display("\n\n------------------------------------------------------");
		$display("mode = %4b (A [%1db] x W [%1db])",mode, m, n);
		$display("------------------------------------------------------\n\n");
		
		// VCD dump file
		$dumpfile(VCD_FILE);
		$dumpvars(0, top_mac_serial2d);
	
		// repeat accumulation cycles
		repeat (10000) begin
		
			// mini accu reset
			rst      = 1;
			//rst_mult = 1; // REMOVED TO AVOID TRIGGERING CLK_SLOW
			w            = 0;
			a            = 0;
			sign_ctr     = 0;
			shift_ctr    = 0;
			#(1*CLK_PERIOD);
			rst      = 0;

			// repeat operations
			repeat (50) begin
				
				// scan operands from file
				status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
				if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
				stimuli_nb++;

				// correct operands for data gating
				w_o = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH; // zero-padded LSBs
				a_o = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH; // zero-padded LSBs

				// serial operation
				shift_ctr    = 0;
				rst_mult     = 1;
				for(int i = 0; i < m+n-1; i++) begin
					if (i==0) 
						shift_ctr = 0;
					else
						shift_ctr = 1;		
					for(int j = max(0,i-m+1); j < min(i,n-1)+1; j++) begin
						@(negedge clk_fast)	
						a = a_o;
						w = w_o;
						i_minus_j = i-j;
						a_sel = i_minus_j[2:0];
						w_sel = j[2:0];
						sign_ctr = (j == n-1)? 1:0;
						shift_ctr = 0;
						rst_mult = 0;
					end
				end
				
			end // repeat 50 operations
			
		end // repeat accumulation cycles

		$stop;
	end // end testing
	
endmodule // pb_serial2d
