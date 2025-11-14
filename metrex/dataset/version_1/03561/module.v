module hybrid_pwm_sd
(
	input clk,
	input n_reset,
	input [15:0] din,
	output dout
);

reg [4:0] pwmcounter;
reg [4:0] pwmthreshold;
reg [33:0] scaledin;
reg [15:0] sigma;
reg out;

assign dout=out;

always @(posedge clk, negedge n_reset) begin
	if(!n_reset)
	begin
		sigma<=16'b00000100_00000000;
		pwmthreshold<=5'b10000;
        pwmcounter<=5'd0;
        scaledin<=34'd0;
	end
	else
	begin
		pwmcounter<=pwmcounter+1;

		if(pwmcounter==pwmthreshold)
			out<=1'b0;

		if(pwmcounter==5'b11111) begin
			scaledin<=33'd134217728 +({1'b0,din}*61440); sigma<=scaledin[31:16]+{5'b000000,sigma[10:0]};	pwmthreshold<=sigma[15:11]; out<=1'b1;
		end

	end
end

endmodule
