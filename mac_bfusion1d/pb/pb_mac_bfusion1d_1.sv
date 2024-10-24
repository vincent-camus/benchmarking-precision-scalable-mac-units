//-----------------------------------------------------
// Design:    pb_mac_bfusion1d
// Version:   1.0
//-----------------------------------------------------
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 0 -> #1  8x8b
//                mode 1 -> #2  8x4b
//-----------------------------------------------------

`timescale 1ns/1ps

module pb_mac_bfusion1d; //#1 8x8
	
	//-------------Testbench parameter---------------------
	parameter  W_CHOSEN_WIDTH;
	parameter  A_CHOSEN_WIDTH;
	parameter  VCD_FILE;
	parameter  STIMULI_MAX;
	parameter  CLK_PERIOD;
	parameter  STIMULI_FILE;
	
	//-------------Design parameter------------------------
	parameter  HEADROOM = 4;
	parameter  SCALABLE_LEVELS = 1;
	
	//-------------Local testbench parameters--------------
	localparam W_ACTIVE_WIDTH  = 2**($clog2(W_CHOSEN_WIDTH)) > 8/(2**SCALABLE_LEVELS)
		? 2**($clog2(W_CHOSEN_WIDTH)) : 8/(2**SCALABLE_LEVELS);
	localparam A_ACTIVE_WIDTH  = 8;

	//-------------Simulation selection--------------------
	bit test_88 = ((W_ACTIVE_WIDTH == 8) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	//bit test_44 = ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 4)) ? 1 : 0;
	//bit test_22 = ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 2)) ? 1 : 0;
	bit test_84 = ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	//bit test_82 = ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	
	//-------------UUT signals-----------------------------
	logic                        clk;
	logic  				         rst;
	logic 				         accu_rst;     

	logic        [ 7:0]          w = '0;  // signed
	logic        [15:0]          a = '0;  // unsigned
	logic signed [15+HEADROOM:0] z;       // signed

	logic signed [ 7:0]          w_88 = '0; 
	logic        [ 7:0]          a_88 = '0; 

	logic        [ 7:0]          w_84 = '0; 
	logic        [15:0]          a_84 = '0;

	logic                        mode = '0; 
	
	//-------------Bench signals---------------------------
	integer mult_exp;
	integer z_exp1,z_exp; //z_exp is the delayed version of z_exp1;
	
	// lines
	logic   [W_CHOSEN_WIDTH-1:0] w_line;
	logic   [A_CHOSEN_WIDTH-1:0] a_line;
	
	// files
	integer                      stimuli_fp;
	integer                      stimuli_nb;  // stimuli counter
	integer                      status;  
		
	//-------------UUT instanciation-----------------------
	top_mac_bfusion1d top_mac_bfusion1d (
		// Inputs
		.clk        (clk),
		.rst        (rst),
		.accu_rst   (accu_rst),
		.a          (a),
		.w          (w),
		.mode       (mode),
		// Outputs
		.z          (z)
	);

	//-------------Clock-----------------------------------
	initial clk = 0;
	always #(CLK_PERIOD/2) clk = ~clk;

	//-------------Bench-------------------------------------
	
	//-----------expected------------
	always @(posedge clk) begin

		if (rst) begin
			mult_exp <= 0;
			z_exp1   <= 0;
		end

		else begin
			unique case (mode)
				//#1  8x8b
				1'b0: mult_exp <= $signed({1'b0, a_88}) * $signed(w_88);

				//#4  8x4b
				1'b1: mult_exp <= $signed({1'b0, a_84[15:8]}) * $signed(w_84[7:4]) + $signed({1'b0, a_84[7:0]}) * $signed(w_84[3:0]);

			endcase
			z_exp1 <= (accu_rst)? '0: $signed(z_exp1)+ $signed(mult_exp);		
		end
		
	end

	always @(posedge clk) begin
		z_exp <= z_exp1;
	end

	//---------data dispatch--------
	
	always_comb begin
		unique case (mode)
			1'b0: begin 
						a = {'0,a_88};

						w = {'0,w_88};
					end

			1'b1: begin 
						a = {'0,a_84};

						w = {'0,w_84};
					end
		endcase
	end	
	
	//-----------testing------------
 	
	initial begin // begin testing
	
		//****************************************************************************************************************************************
		
		// print
		$display("** Info: starting w%0d_a%0d_%1.3f in w%0d_a%0d active mode with %0d stimuli.",
			W_CHOSEN_WIDTH, A_CHOSEN_WIDTH, CLK_PERIOD, W_ACTIVE_WIDTH, A_ACTIVE_WIDTH, STIMULI_MAX);
		
		// open stimuli file
		stimuli_fp = $fopen(STIMULI_FILE, "r");
		stimuli_nb = 0;
		
		// Pre-configuration reset
		rst       = 1;
		accu_rst  = 1;
		mode      = 1'b0;
		@(negedge clk)
		#(5 * CLK_PERIOD);

		//****************************************************************************************************************************************
		
		if (test_88) begin
			$display("\n\n------------------------------------------------------");
			$display("========== BitFusion_top testbench (#1 8x8) ==========");
			$display("------------------------------------------------------\n\n");

			// initial reset
			rst      =  1;
			accu_rst =  0;
			mode     = 1'b0;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion1d);
		
			// repeat accumulation cycles
			repeat (10000) begin
		
				// accu reset
				rst      = 0;
				accu_rst = 1;
				w_88 = '0;
				a_88 = '0;
				@(negedge clk);
			
				// repeat operations
				repeat (50) begin
								
					// scan operands from file
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
				
					// correct operands
					w_88 = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_88 = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
				
					// processing and wait
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);

					// assert
					$display("time =%2d, a =%d, w =%d, z =%d, correct=%d, Yes? %b", $time, a_88, w_88, z, z_exp, (z==z_exp));	
					if(z!=z_exp) $display("\nErrors\n");
					assert ($signed(z==z_exp));
				
				end
			end
		$stop;
		end // end simulation
	
		//****************************************************************************************************************************************
		
		if (test_84) begin
			$display("\n\n------------------------------------------------------");
			$display("========== BitFusion_top testbench (#2 8x4) ==========");
			$display("------------------------------------------------------\n\n");

			// initial reset
			rst      =  1;
			accu_rst =  0;
			mode     = 1'b1;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion1d);
		
			// repeat accumulation cycles
			repeat (10000) begin
		
				// accu reset
				rst      = 0;
				accu_rst = 1;
				a_84 = '0;
				w_84 = '0;
				@(negedge clk);
			
				// repeat operations
				repeat (50) begin
								
					// 1st pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_84[7 :4 ] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_84[15:8 ] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// 2nd pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_84[3 :0 ] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_84[7 :0 ] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// processing and wait
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);

					// assert
					$display("time =%2d, | a1=%d, w1=%d| a2=%d, w2=%d|, z =%d, correct=%d, Yes? %b", $time, a_84[15:8], $signed(w_84[7:4]), a_84[7:0], $signed(w_84[3:0]), $signed(z[12+HEADROOM:0]), z_exp, ($signed(z[12+HEADROOM:0])==z_exp));
					if($signed(z[12+HEADROOM:0])!=z_exp) $display("\nErrors\n");
					assert ($signed(z[12+HEADROOM:0])==z_exp);
				
				end
			end
		$stop;
		end // end simulation

		//****************************************************************************************************************************************
		
	end // end testing
	
endmodule // pb_mac_bfusion1d

