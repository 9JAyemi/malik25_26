

module avalon_to_wb_bridge #(
	parameter DW = 32,	parameter AW = 32	)(
	input 		  clk,
	input 		  rst,
	input [AW-1:0] 	  avm_address_i,
	input [DW/8-1:0]  avm_byteenable_i,
	input 		  avm_read_i,
	output [DW-1:0]   avm_readdata_o,
	input [7:0] 	  avm_burstcount_i,
	input 		  avm_write_i,
	input [DW-1:0] 	  avm_writedata_i,
	output 		  avm_waitrequest_o,
	output 		  avm_readdatavalid_o,
	output [AW-1:0]   wbm_adr_o,
	output [DW-1:0]   wbm_dat_o,
	output [DW/8-1:0] wbm_sel_o,
	output 		  wbm_we_o,
	output 		  wbm_cyc_o,
	output 		  wbm_stb_o,
	output [2:0] 	  wbm_cti_o,
	output [1:0] 	  wbm_bte_o,
	input [DW-1:0] 	  wbm_dat_i,
	input 		  wbm_ack_i,
	input 		  wbm_err_i,
	input 		  wbm_rty_i
);

reg read_access;

always @(posedge clk)
	if (rst)
		read_access <= 0;
	else if (wbm_ack_i | wbm_err_i)
		read_access <= 0;
	else if (avm_read_i)
		read_access <= 1;

reg readdatavalid;
reg [DW-1:0] readdata;
always @(posedge clk) begin
	readdatavalid <= (wbm_ack_i | wbm_err_i) & read_access;
	readdata <= wbm_dat_i;
end

assign wbm_adr_o = avm_address_i;
assign wbm_dat_o = avm_writedata_i;
assign wbm_sel_o =  avm_byteenable_i;
assign wbm_we_o = avm_write_i;
assign wbm_cyc_o = read_access | avm_write_i;
assign wbm_stb_o = read_access | avm_write_i;
assign wbm_cti_o = 3'b111; assign wbm_bte_o = 2'b00;
assign avm_waitrequest_o = !(wbm_ack_i | wbm_err_i);
assign avm_readdatavalid_o = readdatavalid;
assign avm_readdata_o = readdata;

endmodule
