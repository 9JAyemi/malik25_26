
module mux(opA,opB,sum,dsp_sel,out);
	input [3:0] opA,opB;
	input [4:0] sum;
	input [1:0] dsp_sel;
	output [3:0] out;
	
	reg cout;
	
	always @ (sum)
		begin
			if (sum[4] == 1)
				cout <= 4'b0001;
			else
				cout <= 4'b0000;
		end
	
	reg out;
	
	always @(dsp_sel,sum,cout,opB,opA)
		begin
			if (dsp_sel == 2'b00)
				out <= sum[3:0];
			else if (dsp_sel == 2'b01)
				out <= cout;
			else if (dsp_sel == 2'b10)
				out <= opB;
			else if (dsp_sel == 2'b11)
				out <= opA;
		end

endmodule
