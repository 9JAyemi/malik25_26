module EdgeDelay(clk, sigIn, waitCnt, sigOut, diagOut);


parameter WAIT_CNT_SIZE=11;
parameter INVERT_FLAG=1'b0; parameter MIN_WAIT=3'b10; input clk, sigIn;
input [WAIT_CNT_SIZE-1:0] waitCnt;
output sigOut;
output diagOut; reg [WAIT_CNT_SIZE-1:0] posEdgeDelayTimer;
reg [WAIT_CNT_SIZE-1:0] negEdgeDelayTimer;

reg sigOutReg;
reg sigLast;
reg sigReg;

reg resetFlag; initial begin
	#0
	sigOutReg=1'b0;
	posEdgeDelayTimer=1'b0;
	negEdgeDelayTimer=1'b0;
	sigLast=1'b0;
end

reg posEdgeReg, posEdgeRegLast, negEdgeReg, negEdgeRegLast;

always @(posedge sigIn) begin
	posEdgeReg=~posEdgeReg;
end

always @(negedge sigIn) begin
	negEdgeReg=~negEdgeReg;
end

always @(posedge clk) begin
	sigReg=sigIn;
	
	if(posEdgeRegLast!=posEdgeReg && posEdgeDelayTimer>MIN_WAIT) begin
		posEdgeDelayTimer=1'b0; posEdgeRegLast=posEdgeReg;
	end else	if(negEdgeRegLast!=negEdgeReg && negEdgeDelayTimer>MIN_WAIT) begin
		negEdgeDelayTimer=1'b0; negEdgeRegLast=negEdgeReg;
		resetFlag=~resetFlag;
	end
	
	
	
	
	if(posEdgeDelayTimer<waitCnt) begin
		posEdgeDelayTimer=posEdgeDelayTimer+1'b1;
	end else if(posEdgeDelayTimer==waitCnt) begin posEdgeDelayTimer=posEdgeDelayTimer+1'b1;
		sigOutReg=1'b1; end else

	if(negEdgeDelayTimer<waitCnt) begin
		negEdgeDelayTimer=negEdgeDelayTimer+1'b1;
	end else if(negEdgeDelayTimer==waitCnt) begin negEdgeDelayTimer=negEdgeDelayTimer+1'b1;
		sigOutReg=1'b0; end end

assign sigOut=sigOutReg; assign diagOut=negEdgeReg;

endmodule




