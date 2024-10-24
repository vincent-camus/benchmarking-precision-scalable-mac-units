// Auto-generated on 2018/06/11 17:26
// Script:   iclabsrv3:/iclabqnap/home/camus/multi-precision-mac/scripts/auto_batch_generator_3.pl
// Listing:  lists/serial.csv
// Template: templates/top_mac_serial.sv
//
//-----------------------------------------------------
// Author:    Vincent Camus
// Design:    top_mac_serial
// Function:  input registers, FSM overhead
// Notes:     secondary accu clock, but kept fsm_accu signal
//-----------------------------------------------------


module top_mac_serial (clk, clk_accu, rst, config_w, fsm_last, fsm_accu, w_serial, a, z);
	
	//-------------Parameters------------------------------
	parameter  W_WIDTH         = 8; // max bits for w
	parameter  A_WIDTH         = 8;
	parameter  PLUS_WIDTH      = 4; // extra for the MAC accumulator
	parameter  N_WIDTH         = 2;
	parameter  CONFIG_W_WIDTH  = 2; // 1-bit signal per clock-gated block
	
	//-------------Local parameters------------------------
	localparam Z_WIDTH         = W_WIDTH+A_WIDTH+PLUS_WIDTH;
	
	//-------------Inputs----------------------------------
	
	// general
	input                       clk;
	input                       clk_accu;
	input                       rst;

	// external MAC FSM
	input                       fsm_last;
	input                       fsm_accu;
	
	// operands
	input         [N_WIDTH-1:0] w_serial;
	input         [A_WIDTH-1:0] a;
	
	// configuration (unconstrained)
	input  [CONFIG_W_WIDTH-1:0] config_w; // LSB clock-gates LSBs
	
	//-------------Outputs---------------------------------
	output        [Z_WIDTH-1:0] z;
	
	//-------------Internal signals------------------------
	reg                         rst_reg;
	reg                         fsm_last_reg;
	reg                         fsm_accu_reg;
	reg           [N_WIDTH-1:0] w_serial_reg;
	reg           [A_WIDTH-1:0] a_reg;
	reg    [CONFIG_W_WIDTH-1:0] config_w_reg;
	
	//-------------Datapath--------------------------------
	
	// synchronous rst of the MAC module
	always_ff @(posedge clk)
		rst_reg <= rst;
	
	// input registers
	always_ff @(posedge clk) begin
		if (rst == 1) begin
			fsm_last_reg  <= 0;
			fsm_accu_reg  <= 0;
			w_serial_reg  <= 0;
			a_reg         <= 0;
		end
		else begin
			fsm_last_reg  <= fsm_last;
			fsm_accu_reg  <= fsm_accu;
			w_serial_reg  <= w_serial;
			a_reg         <= a;
		end
	end

	// MAC module
	mac_serial #(
		// Parameters
		.W_WIDTH        (W_WIDTH),
		.A_WIDTH        (A_WIDTH),
		.PLUS_WIDTH     (PLUS_WIDTH),
		.N_WIDTH        (N_WIDTH),
		.CONFIG_W_WIDTH (CONFIG_W_WIDTH)
	)
	mac (
		// Inputs
		.clk      (clk),
		.clk_accu (clk_accu),
		.rst      (rst_reg),
		.config_w (config_w),
		.fsm_last (fsm_last_reg),
		.fsm_accu (fsm_accu_reg),
		.w_serial (w_serial_reg),
		.a        (a_reg),
		// Outputs
		.z        (z)
	);
	
endmodule // top_mac_serial
