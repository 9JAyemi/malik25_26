module driver (clk, state, enable);


input clk;
input [6:0] state; output enable; reg enableReg; reg [2:0] settleTimeCntr;
reg [4:0] enableOnCntr;

reg settleTimeFlag; reg enableOnFlag; reg [6:0] stateLast; parameter SETTLE_TIME=3'b111;
parameter ENABLE_ON_TIME=5'b11111;

initial begin
	stateLast=7'b0; settleTimeCntr=3'b0; enableOnCntr=5'b0; settleTimeFlag=1'b0; enableOnFlag=1'b0; enableReg=1'b0; end

always @(posedge clk) begin
	if(|(stateLast - state)) begin settleTimeCntr=3'b0;
		
		settleTimeFlag=1'b1;
		
		stateLast=state; end
	
	if(settleTimeFlag) begin
		if(settleTimeCntr==SETTLE_TIME) begin
			settleTimeFlag=1'b0; enableOnFlag=1'b1; settleTimeCntr=3'b0; enableOnCntr=5'b0;
		end else settleTimeCntr=settleTimeCntr+3'b1; end
	
	if(enableOnFlag) begin
		if(enableOnCntr==ENABLE_ON_TIME) begin
			enableReg=1'b0; enableOnFlag=1'b0; enableOnCntr=5'b0; end else begin
			enableReg=1'b1; enableOnCntr=enableOnCntr+5'b1; end
	end
end

assign enable=enableReg; endmodule
