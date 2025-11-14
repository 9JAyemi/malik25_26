module asr(value1, value2, shift_hex, value_out, EN);
	input [31:0] value1, value2;
	input [3:0] shift_hex;
	output [31:0] value_out;
	input EN;

	wire or_unary = |value2[31:5];
	wire value2_shrink = value2[4:0];

	wire [4:0] shift_amt = (value2_shrink== 32'b0) ? 
		( {1'b0, shift_hex} + 5'b1) : (value2_shrink + {1'b0, shift_hex});

	assign value_out = (or_unary==1'b1) ? 32'b0 : (
		(shift_amt == 5'b00000) ? value1[31:0] :
		(shift_amt == 5'b00001) ? {{01{value1[31]}}, value1[31:01]} :
		(shift_amt == 5'b00010) ? {{02{value1[31]}}, value1[31:02]} :
		(shift_amt == 5'b00011) ? {{03{value1[31]}}, value1[31:03]} :
		(shift_amt == 5'b00100) ? {{04{value1[31]}}, value1[31:04]} :
		(shift_amt == 5'b00101) ? {{05{value1[31]}}, value1[31:05]} :
		(shift_amt == 5'b00110) ? {{06{value1[31]}}, value1[31:06]} :
		(shift_amt == 5'b00111) ? {{07{value1[31]}}, value1[31:07]} :
		(shift_amt == 5'b01000) ? {{08{value1[31]}}, value1[31:08]} :
		(shift_amt == 5'b01001) ? {{09{value1[31]}}, value1[31:09]} :
		(shift_amt == 5'b01010) ? {{10{value1[31]}}, value1[31:10]} :
		(shift_amt == 5'b01011) ? {{11{value1[31]}}, value1[31:11]} :
		(shift_amt == 5'b01100) ? {{12{value1[31]}}, value1[31:12]} :
		(shift_amt == 5'b01101) ? {{13{value1[31]}}, value1[31:13]} :
		(shift_amt == 5'b01110) ? {{14{value1[31]}}, value1[31:14]} :
		(shift_amt == 5'b01111) ? {{15{value1[31]}}, value1[31:15]} :
		(shift_amt == 5'b10000) ? {{16{value1[31]}}, value1[31:16]} :
		(shift_amt == 5'b10001) ? {{17{value1[31]}}, value1[31:17]} :
		(shift_amt == 5'b10010) ? {{18{value1[31]}}, value1[31:18]} :
		(shift_amt == 5'b10011) ? {{19{value1[31]}}, value1[31:19]} :
		(shift_amt == 5'b10100) ? {{20{value1[31]}}, value1[31:20]} :
		(shift_amt == 5'b10101) ? {{21{value1[31]}}, value1[31:21]} :
		(shift_amt == 5'b10110) ? {{22{value1[31]}}, value1[31:22]} :
		(shift_amt == 5'b10111) ? {{23{value1[31]}}, value1[31:23]} :
		(shift_amt == 5'b11000) ? {{24{value1[31]}}, value1[31:24]} :
		(shift_amt == 5'b11001) ? {{25{value1[31]}}, value1[31:25]} :
		(shift_amt == 5'b11010) ? {{26{value1[31]}}, value1[31:26]} :
		(shift_amt == 5'b11011) ? {{27{value1[31]}}, value1[31:27]} :
		(shift_amt == 5'b11100) ? {{28{value1[31]}}, value1[31:28]} :
		(shift_amt == 5'b11101) ? {{29{value1[31]}}, value1[31:29]} :
		(shift_amt == 5'b11110) ? {{30{value1[31]}}, value1[31:30]} :
		(shift_amt == 5'b11111) ? {{31{value1[31]}}, value1[31]} : 32'b0);
endmodule