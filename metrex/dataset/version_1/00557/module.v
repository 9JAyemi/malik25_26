module twobitmux(in, s, out);
	input wire[1: 0] in;
	input wire s;
	output wire out;
	assign out = (s == 1'b0) ? in[0] : in[1];
endmodule

module eightbitmux(in, s, out);
	input wire[7: 0] in;
	input wire[2: 0] s;
	output wire out;
	wire[5: 0] _out;
	twobitmux m1({in[0], in[1]}, s[0], _out[0]);
	twobitmux m2({in[2], in[3]}, s[0], _out[1]);
	twobitmux m3({in[4], in[5]}, s[0], _out[2]);
	twobitmux m4({in[6], in[7]}, s[0], _out[3]);
	twobitmux m5({_out[0], _out[1]}, s[1], _out[4]);
	twobitmux m6({_out[2], _out[3]}, s[1], _out[5]);
	twobitmux m7({_out[4], _out[5]}, s[2], out);
endmodule