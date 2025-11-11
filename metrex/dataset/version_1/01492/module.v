`define S_INTRCTLR_IDLE				3'd0
`define S_INTRCLTR_WORKING			3'd1
`define S_INTRCLTR_COMPLETE			3'd2
`define S_INTRCLTR_CLEAR_LEGACY		3'd3
`define S_INTRCLTR_CLEARING_LEGACY	3'd4
`define S_INTRCLTR_DONE				3'd5

module interrupt_controller (
	input CLK,						input RST,						input INTR,						input INTR_LEGACY_CLR,			output INTR_DONE,				input CONFIG_INTERRUPT_MSIENABLE,	output CFG_INTERRUPT_ASSERT,	input INTR_MSI_RDY,		output INTR_MSI_REQUEST			);

reg		[2:0]	rState=`S_INTRCTLR_IDLE;
reg		[2:0]	rStateNext=`S_INTRCTLR_IDLE;
reg				rIntr=0;
reg				rIntrAssert=0;

assign INTR_DONE = (rState == `S_INTRCLTR_DONE);
assign INTR_MSI_REQUEST = rIntr;
assign CFG_INTERRUPT_ASSERT = rIntrAssert;

always @(*) begin
	case (rState)

	`S_INTRCTLR_IDLE : begin
		if (INTR) begin
			rIntr = 1;
			rIntrAssert = !CONFIG_INTERRUPT_MSIENABLE;
			rStateNext = (INTR_MSI_RDY ? `S_INTRCLTR_COMPLETE : `S_INTRCLTR_WORKING);
		end 
		else begin
			rIntr = 0;
			rIntrAssert = 0;
			rStateNext = `S_INTRCTLR_IDLE;
		end
	end

	`S_INTRCLTR_WORKING : begin
		rIntr = 1;
		rIntrAssert = !CONFIG_INTERRUPT_MSIENABLE;
		rStateNext = (INTR_MSI_RDY ? `S_INTRCLTR_COMPLETE : `S_INTRCLTR_WORKING);
	end

	`S_INTRCLTR_COMPLETE : begin
		rIntr = 0;
		rIntrAssert = !CONFIG_INTERRUPT_MSIENABLE;
		rStateNext = (CONFIG_INTERRUPT_MSIENABLE ? `S_INTRCLTR_DONE : `S_INTRCLTR_CLEAR_LEGACY);
	end

	`S_INTRCLTR_CLEAR_LEGACY : begin
		if (INTR_LEGACY_CLR) begin
			rIntr = 1;
			rIntrAssert = 0;
			rStateNext = (INTR_MSI_RDY ? `S_INTRCLTR_DONE : `S_INTRCLTR_CLEARING_LEGACY);
		end 
		else begin
			rIntr = 0;
			rIntrAssert = 1;
			rStateNext = `S_INTRCLTR_CLEAR_LEGACY;
		end
	end

	`S_INTRCLTR_CLEARING_LEGACY : begin
		rIntr = 1;
		rIntrAssert = 0;
		rStateNext = (INTR_MSI_RDY ? `S_INTRCLTR_DONE : `S_INTRCLTR_CLEARING_LEGACY);
	end

	`S_INTRCLTR_DONE : begin
		rIntr = 0;
		rIntrAssert = 0;
		rStateNext = `S_INTRCTLR_IDLE;
	end
	
	default: begin
		rIntr = 0;
		rIntrAssert = 0;
		rStateNext = `S_INTRCTLR_IDLE;
	end
	
	endcase
end

always @(posedge CLK) begin
	if (RST)
		rState <= #1 `S_INTRCTLR_IDLE;
	else
		rState <= #1 rStateNext;
end

endmodule

