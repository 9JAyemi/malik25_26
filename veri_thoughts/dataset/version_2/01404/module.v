module alu(
		input		[3:0]	ctl,
		input		[31:0]	a, b,
		output reg	[31:0]	out,
		output				zero,
		output				oflow);

	wire [31:0] sub_ab;
	wire [31:0] add_ab;
	wire 		oflow_add;
	wire 		oflow_sub;
	wire 		slt;

	assign zero = (0 == out);

	assign sub_ab = a - b;
	assign add_ab = a + b;

	assign oflow_add = (a[31] == b[31] && add_ab[31] != a[31]) ? 1 : 0;
	assign oflow_sub = (a[31] == b[31] && sub_ab[31] != a[31]) ? 1 : 0;

	assign oflow = (ctl == 4'b0010) ? oflow_add : oflow_sub;

	assign slt = oflow_sub ? ~(a[31]) : a[31];

	always @(*) begin
		case (ctl)
			4'd2:  out <= add_ab;				
			4'd0:  out <= a & b;				
			4'd12: out <= ~(a | b);				
			4'd1:  out <= a | b;				
			4'd7:  out <= {{31{1'b0}}, slt};	
			4'd6:  out <= sub_ab;				
			4'd13: out <= a ^ b;				
			default: out <= 0;
		endcase
	end

endmodule