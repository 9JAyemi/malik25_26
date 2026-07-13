
module right_barrel_shifter(
	input [7:0] d_in,
	input [2:0] shift_amount,
	output reg [7:0] d_out
);

always @* begin
	case (shift_amount)
		0 : d_out = d_in;
		1 : d_out = {d_in[0], d_in[7:1]}; 2 : d_out = {d_in[1:0], d_in[7:2]};
		3 : d_out = {d_in[2:0], d_in[7:3]};
		4 : d_out = {d_in[3:0], d_in[7:4]};
		5 : d_out = {d_in[4:0], d_in[7:5]};
		6 : d_out = {d_in[5:0], d_in[7:6]};
		7 : d_out = 0;
	endcase
end 

endmodule
