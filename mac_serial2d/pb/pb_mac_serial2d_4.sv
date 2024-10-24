//-------------------------------------------------------------
// Design:        testbench for 2D multi-4bit-serial MAC 
// Description:   2D multi-4bit-serial MAC unit from Loom
// Version:       1.5
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 000 -> 8x8b
//                mode 111 -> 4x4b
//                mode 001 -> 8x4b    
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
	parameter  N_WIDTH  = 4;
	
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
	logic                       rst_delayed       = 0;

	logic                       rst_mult          = 0;
	logic                       rst_mult_delayed = '0;
	logic                       rst_mult_delayed2 = '0;
	// config
	logic                 [2:0] mode         = 3'b000;
	
	// MAC FSM
	logic                       shift_ctr    = 0;
	logic                       sign_ctr     = 0;
	logic                       w_sel        = 0;
	logic                       a_sel        = 0;

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

	logic                [19:0] z_exp, z_exp_delayed, z_exp_delayed2, z_exp_delayed3;

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
	//initial rst_mult_delayed = 0;
	//always rst_mult_delayed = #(0.5*CLK_PERIOD) rst_mult;  // if the tool is bug-free, there should be #(1*CLK_PERIOD)
	always #(CLK_PERIOD) rst_mult_delayed2 = rst_mult_delayed;
	always #(CLK_PERIOD) rst_mult_delayed  = rst_mult;	
	//always_ff @(posedge clk_fast)
	//	rst_mult_delayed <= rst_mult;
		
	always_comb begin
		if (rst) begin
			clk_slow <= clk_fast;
		end
        else begin
			clk_slow <= rst_mult_delayed2 & clk_fast;
		end
	end
	//-----------------------------------------------------

	always_comb begin
		unique case (mode)
			3'b000: begin m <= 2; n <= 2; end
			3'b111: begin m <= 1; n <= 1; end
			3'b001: begin m <= 2; n <= 1; end
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

	//-------Assist signal for Assertion------	
	//initial rst_delayed = 0;
	//always rst_delayed = #(0.5*CLK_PERIOD) rst;    // if the tool is bug-free, there should be #(1*CLK_PERIOD)
	always #(CLK_PERIOD) rst_delayed  = rst;
		
	//-----------expected------------

	//initial z_exp_delayed = '0;
	//always z_exp_delayed = #(1*CLK_PERIOD) z_exp;  // if the tool is bug-free, there should be #(2*CLK_PERIOD)
	always #(CLK_PERIOD) z_exp_delayed2 = z_exp_delayed;
	always #(CLK_PERIOD) z_exp_delayed  = z_exp;

	always_comb begin
		if (rst_delayed) begin
			z_exp_delayed3 <= '0;
		end
        else begin
			z_exp_delayed3 <= z_exp_delayed2;
		end
	end


	
	property accumulation;
		(!rst)
		// , $display("time=%-8d, a=%d, w=%d, z=%d, z_exp=%d, Yes? %b", $time, $unsigned(a_line), $signed(w_line), $signed(z), $signed(z_exp), (z==z_exp))
		|-> (z_exp_delayed3 == z)
	endproperty
	//always @(negedge clk_slow) assert property (accumulation);
	
	//-----------testing------------
	
	initial begin

		// print
		$display("** Info: starting w%0d_a%0d_%1.3f in w%0d_a%0d active mode with %0d stimuli.",
			W_CHOSEN_WIDTH, A_CHOSEN_WIDTH, CLK_PERIOD, W_ACTIVE_WIDTH, A_ACTIVE_WIDTH, STIMULI_MAX);
		
		// open stimuli file
		stimuli_fp = $fopen(STIMULI_FILE, "r");
		stimuli_nb = 0;
		
		// Pre-configuration reset
		mode      = 3'b000;
		rst       = 1;
		//rst_mult  = 1;
		w            = 0;
		a            = 0;
		sign_ctr     = 0;
		shift_ctr    = 0;
		repeat (5) @(negedge clk_fast);
	
		//****************************************************************************************************************************************
		
		// choose configuration and continue reset
		if      ((W_ACTIVE_WIDTH == 8) && (A_ACTIVE_WIDTH == 8)) mode <= 3'b000;
		else if ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 4)) mode <= 3'b111;
		else if ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 8)) mode <= 3'b001;
		else mode <= 3'bxxx;
		repeat (5) @(negedge clk_fast);
		
		$display("\n\n------------------------------------------------------");
		$display("mode = %3b (A [%1db] x W [%1db])",mode, m*4, n*4);
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
			z_exp        = 0;

			#(1*CLK_PERIOD);
			rst          = 0;

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

				case (mode)
					3'b000: z_exp = $signed(z_exp) + ($signed({1'b0,a     })*$signed(w)           );
					3'b111: z_exp = $signed(z_exp) + ($signed({1'b0,a[3:0]})*$signed(w[3:0]) << 8 );
					3'b001: z_exp = $signed(z_exp) + ($signed({1'b0,a     })*$signed(w[3:0]) << 4 );
				endcase

				
			end // repeat 50 operations
			
		end // repeat accumulation cycles

		$stop;
	end // end testing
	
endmodule // pb_serial2d
