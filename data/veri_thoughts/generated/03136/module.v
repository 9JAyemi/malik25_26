

module radix2_linediv(
		input wire [1:0] iSOURCE_DIVIDEND,
		input wire [31:0] iSOURCE_DIVISOR,
		input wire [30:0] iSOURCE_R,
		output wire [1:0] oOUT_DATA_Q,
		output wire [30:0] oOUT_DATA_R
	);
			


	
	wire q0, q1;
	wire [30:0] r0, r1;
	
	
	assign {q0, r0} = func_radix2_linediv({iSOURCE_R, iSOURCE_DIVIDEND[1]}, iSOURCE_DIVISOR);
	assign {q1, r1} = func_radix2_linediv({r0, iSOURCE_DIVIDEND[0]}, iSOURCE_DIVISOR);
	
	
	
	function [31:0] func_radix2_linediv;
		input [31:0] func_dividend;
		input [31:0] func_divisor;
		reg [31:0] func_sub;
		begin
			func_sub = func_dividend + (~func_divisor + 32'h00000001);
			if(func_sub[31])begin
				func_radix2_linediv = {1'b0, func_dividend[30:0]};
			end
			else begin
				func_radix2_linediv = {1'b1, func_sub[30:0]};
			end
		end
	endfunction
	
	
	assign oOUT_DATA_Q = {q0, q1};
	assign oOUT_DATA_R = r1;
	
endmodule

			