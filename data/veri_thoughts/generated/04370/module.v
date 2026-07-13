
module even_odd(in, out);
input [3:0] in;
output [1:0] out;

assign out = (in % 2 == 0) ? (in * 2) : (in / 2); // Use a conditional operator to assign the output based on the input's parity

endmodule
