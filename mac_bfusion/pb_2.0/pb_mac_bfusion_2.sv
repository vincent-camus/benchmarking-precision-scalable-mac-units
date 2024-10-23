//-----------------------------------------------------
// File Name: pb_mac_bfusion_1.sv
// Design:    pb_mac_bfusion
//-----------------------------------------------------
// Working mode:  Always do half-signed multiplication (unsigned activation * signed weight)
//                mode 000 -> #1  8x8b -> activate 16 bits / 16 bits + headroom register  
//                mode 010 -> #4  4x4b -> activate 10 bits / 10 bits + headroom register 
//                mode 011 -> #16 2x2b -> activate  8 bits /  8 bits + headroom register
//                mode 110 -> #2  8x4b -> activate 13 bits / 13 bits + headroom register
//                mode 111 -> #4  8x2b -> activate 12 bits / 12 bits + headroom register          
//-----------------------------------------------------

`timescale 1ns/1ps

module pb_mac_bfusion; //#1 8x8
	
	//-------------Testbench parameter---------------------
	parameter  W_CHOSEN_WIDTH;
	parameter  A_CHOSEN_WIDTH;
	parameter  VCD_FILE;
	parameter  STIMULI_MAX;
	parameter  CLK_PERIOD;
	parameter  STIMULI_FILE;
	
	//-------------Design parameter------------------------
	parameter  HEADROOM = 4;
	parameter  SCALABLE_LEVELS;
	
	//-------------Local testbench parameters--------------
	localparam W_ACTIVE_WIDTH  = 2**($clog2(W_CHOSEN_WIDTH)) > 8/(2**SCALABLE_LEVELS)
		? 2**($clog2(W_CHOSEN_WIDTH)) : 8/(2**SCALABLE_LEVELS);
	localparam A_ACTIVE_WIDTH  = 2**($clog2(A_CHOSEN_WIDTH)) > 8/(2**SCALABLE_LEVELS)
		? 2**($clog2(A_CHOSEN_WIDTH)) : 8/(2**SCALABLE_LEVELS);

	//-------------Simulation selection--------------------
	bit test_88 = ((W_ACTIVE_WIDTH == 8) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	bit test_44 = ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 4)) ? 1 : 0;
	bit test_22 = ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 2)) ? 1 : 0;
	bit test_84 = ((W_ACTIVE_WIDTH == 4) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	bit test_82 = ((W_ACTIVE_WIDTH == 2) && (A_ACTIVE_WIDTH == 8)) ? 1 : 0;
	
	//-------------UUT signals-----------------------------
	logic                        clk, rst, accu_rst;

	logic        [31:0]          w = '0;  // signed
	logic        [31:0]          a = '0;  // unsigned
	logic signed [15+HEADROOM:0] z;       // signed

	logic signed          [ 7:0] w_88 = '0; 
	logic                 [ 7:0] a_88 = '0; 

	logic                 [15:0] w_44 = '0; 
	logic                 [15:0] a_44 = '0; 

	logic                 [31:0] w_22 = '0; 
	logic                 [31:0] a_22 = '0; 

	logic                 [15:0] a_84 = '0;
	logic                 [ 7:0] w_84 = '0;

	logic                 [31:0] a_82 = '0;  
	logic                 [ 7:0] w_82 = '0;
	
	logic                  [2:0] mode = '0; // always 3 bits
	logic    [SCALABLE_LEVELS:0] config_aw; // depends on design
	
	//-------------Bench signals---------------------------
	integer                      mult_exp;
	integer                      z_exp1, z_exp; //z_exp is the delayed version of z_exp1;
	
	// lines
	logic   [W_CHOSEN_WIDTH-1:0] w_line;
	logic   [A_CHOSEN_WIDTH-1:0] a_line;
	
	// files
	integer                      stimuli_fp;
	integer                      stimuli_nb;  // stimuli counter
	integer                      status;  
		
	//-------------UUT instanciation-----------------------
	top_mac_bfusion top_mac_bfusion (
		// Inputs
		.clk        (clk),
		.rst        (rst),
		.accu_rst   (accu_rst),
		.a          (a),
		.w          (w),
		.config_aw  (config_aw),
		// Outputs
		.z          (z)
	);

	//-------------Clock-----------------------------------
	initial clk = 0;
	always #(CLK_PERIOD/2) clk = ~clk;

	//-------------Mode-------------------------------------
	assign config_aw = mode[2:2-SCALABLE_LEVELS];

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
				3'b000: mult_exp <= $signed({1'b0, a_88}) * $signed(w_88);

				//#4  4x4b
				3'b010: mult_exp <= $signed({1'b0, a_44[15:12]}) * $signed(w_44[15:12]) + $signed({1'b0, a_44[11:8]}) * $signed(w_44[11:8]) +
									$signed({1'b0, a_44[ 7: 4]}) * $signed(w_44[ 7: 4]) + $signed({1'b0, a_44[ 3:0]}) * $signed(w_44[ 3:0]);

				//#16 2x2b				
				3'b011: mult_exp <= $signed({1'b0, a_22[31:30]}) * $signed(w_22[31:30]) + $signed({1'b0, a_22[29:28]}) * $signed(w_22[29:28]) +
									$signed({1'b0, a_22[27:26]}) * $signed(w_22[27:26]) + $signed({1'b0, a_22[25:24]}) * $signed(w_22[25:24]) +
									$signed({1'b0, a_22[23:22]}) * $signed(w_22[23:22]) + $signed({1'b0, a_22[21:20]}) * $signed(w_22[21:20]) +
									$signed({1'b0, a_22[19:18]}) * $signed(w_22[19:18]) + $signed({1'b0, a_22[17:16]}) * $signed(w_22[17:16]) +
									$signed({1'b0, a_22[15:14]}) * $signed(w_22[15:14]) + $signed({1'b0, a_22[13:12]}) * $signed(w_22[13:12]) +
									$signed({1'b0, a_22[11:10]}) * $signed(w_22[11:10]) + $signed({1'b0, a_22[ 9: 8]}) * $signed(w_22[ 9: 8]) +
									$signed({1'b0, a_22[ 7: 6]}) * $signed(w_22[ 7: 6]) + $signed({1'b0, a_22[ 5: 4]}) * $signed(w_22[ 5: 4]) +
									$signed({1'b0, a_22[ 3: 2]}) * $signed(w_22[ 3: 2]) + $signed({1'b0, a_22[ 1: 0]}) * $signed(w_22[ 1: 0]);

				//#2  8x4b
				3'b110: mult_exp <= $signed({1'b0, a_84[15:8]}) * $signed(w_84[7:4]) + $signed({1'b0, a_84[7:0]}) * $signed(w_84[3:0]);

				//#4  8x2b
				3'b111: mult_exp <= $signed({1'b0, a_82[31:24]}) * $signed(w_82[7:6]) + $signed({1'b0, a_82[23:16]}) * $signed(w_82[5:4]) +
									$signed({1'b0, a_82[15: 8]}) * $signed(w_82[3:2]) + $signed({1'b0, a_82[ 7: 0]}) * $signed(w_82[1:0]);
				
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
			3'b000: begin 
						a = {'0,a_88};
						w = {'0,w_88};
					end
			3'b010: begin 
						a = {'0,a_44};
						w = {'0,w_44};
					end
			3'b011: begin 
						a = {'0,a_22};
						w = {'0,w_22};
					end
			3'b110: begin 
						a = {'0,a_84};
						w = {'0,w_84};
					end
			3'b111: begin 
						a = {'0,a_82};
						w = {'0,w_82};
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
		mode = 3'b000;
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
			mode = 3'b000;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion);
		
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
		
		if (test_44) begin
			$display("\n\n------------------------------------------------------");
			$display("========== BitFusion_top testbench (#4 4x4) ==========");
			$display("------------------------------------------------------\n\n");

			// initial reset
			rst      =  1;
			accu_rst =  0;
			mode     = 3'b010;	
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion);
		
			// repeat accumulation cycles
			repeat (10000) begin
		
				// accu reset
				rst      = 0;
				accu_rst = 1;
				a_44 = '0;
				w_44 = '0;
				@(negedge clk);
			
				// repeat operations
				repeat (50) begin
								
					// 1st pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_44[15:12] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_44[15:12] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					// 2nd pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_44[11: 8] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_44[11: 8] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					// 3rd pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_44[ 7: 4] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_44[ 7: 4] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					// 4th pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_44[ 3: 0] = w_line << W_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_44[ 3: 0] = a_line << A_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
				
					// processing and wait
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);

					// assert
					$display("time =%0d| a1=%d, w1=%d| a2=%d, w2=%d| a3=%d, w3=%d| a4=%d, w4=%d| z =%d, correct=%d, Yes? %b", $time, a_44[15:12], $signed(w_44[15:12]), a_44[11:8], $signed(w_44[11:8]), a_44[7:4], $signed(w_44[7:4]), a_44[3:0], $signed(w_44[3:0]), $signed(z[9+HEADROOM:0]), z_exp, ($signed(z[9+HEADROOM:0])==z_exp));	
					if($signed(z[9+HEADROOM:0])!=z_exp) $display("\nErrors\n");
					assert ($signed(z[9+HEADROOM:0])==z_exp);	
				
				end
			end
		$stop;
		end // end simulation
		
		//****************************************************************************************************************************************
		
		if (test_22) begin
			$display("\n\n------------------------------------------------------");
			$display("========== BitFusion_top testbench (#16 2x2) ==========");
			$display("------------------------------------------------------\n\n");

			// initial reset
			rst      =  1;
			accu_rst =  0;
			mode     = 3'b011;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion);
		
			// repeat accumulation cycles
			repeat (10000) begin
		
				// accu reset
				rst      = 0;
				accu_rst = 1;
				a_22 = '0;
				w_22 = '0;
				@(negedge clk);
			
				// repeat operations
				repeat (50) begin
								
					// pair of operands 1-4
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[31:30] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[31:30] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[29:28] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[29:28] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[27:26] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[27:26] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[25:24] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[25:24] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					// pair of operands 5-8
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[23:22] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[23:22] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[21:20] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[21:20] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[19:18] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[19:18] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[17:16] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[17:16] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// pair of operands 9-12
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[15:14] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[15:14] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[13:12] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[13:12] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
		
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[11:10] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[11:10] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[ 9: 8] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[ 9: 8] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// pair of operands 13-16					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[ 7: 6] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[ 7: 6] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[ 5: 4] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[ 5: 4] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;
					
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[ 3: 2] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[ 3: 2] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_22[ 1: 0] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_22[ 1: 0] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;					
				
					// processing and wait
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);

					// assert
					$display("time =%2d, a =%d, w =%d, z =%d, correct=%d, Yes? %b", $time, a_22, w_22, $signed(z[7+HEADROOM:0]), z_exp, ($signed(z[7+HEADROOM:0])==z_exp));
					if($signed(z[7+HEADROOM:0])!=z_exp) $display("\nErrors\n");
					assert ($signed(z[7+HEADROOM:0])==z_exp);
				
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
			mode     = 3'b110;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion);
		
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
		
		if (test_82) begin
			$display("\n\n------------------------------------------------------");
			$display("========== BitFusion_top testbench (#4 8x2) ==========");
			$display("------------------------------------------------------\n\n");

			// initial reset
			rst      =  1;
			accu_rst =  0;
			mode     = 3'b111;
			@(negedge clk)
			#(5 * CLK_PERIOD);
	
			// VCD dump file
			$dumpfile(VCD_FILE);
			$dumpvars(0, top_mac_bfusion);
		
			// repeat accumulation cycles
			repeat (10000) begin
		
				// accu reset
				rst      = 0;
				accu_rst = 1;
				a_82 = '0;
				w_82 = '0;
				@(negedge clk);
			
				// repeat operations
				repeat (50) begin
				
					// 1st pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_82[7 :6 ] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_82[31:24] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// 2nd pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_82[5 :4 ] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_82[23:16] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// 3rd pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_82[3 :2 ] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_82[15:8 ] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// 4th pair of operands
					status = $fscanf(stimuli_fp, "%b,%b", w_line, a_line);
					if((status != 2) || (stimuli_nb > STIMULI_MAX)) $stop;
					stimuli_nb++;
					w_82[1 :0 ] = w_line; // << AW_ACTIVE_WIDTH-W_CHOSEN_WIDTH;
					a_82[7 :0 ] = a_line; // << AW_ACTIVE_WIDTH-A_CHOSEN_WIDTH;

					// processing and wait
					rst      = 0;
					accu_rst = 0;
					@(negedge clk);

					// assert
					$display("time =%2d, | a1=%d, w1=%d| a2=%d, w2=%d|, | a3=%d, w3=%d| a4=%d, w4=%d|, z =%d, correct=%d, Yes? %b", $time, a_82[31:24], $signed(w_82[7:6]), a_82[23:16], $signed(w_82[5:4]), a_82[15:8], $signed(w_82[3:2]), a_82[7:0], $signed(w_82[1:0]), $signed(z[11+HEADROOM:0]), z_exp, ($signed(z[11+HEADROOM:0])==z_exp));		
					if($signed(z[11+HEADROOM:0])!=z_exp) $display("\nErrors\n");
					assert ($signed(z[11+HEADROOM:0])==z_exp);
				
				end
			end
		$stop;
		end // end simulation

		//****************************************************************************************************************************************
		
	end // end testing
	
endmodule // pb_mac_bfusion

