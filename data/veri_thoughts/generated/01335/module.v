module ripple_carry_adder(clock, a_in, b_in, out);

parameter BITS = 8;

input clock;
input [BITS-1:0] a_in;
input [BITS-1:0] b_in;
output [BITS-1:0] out;

wire [BITS:0] carry;
assign carry[0] = 1'b0;

genvar i;
generate
  for (i = 0; i < BITS; i = i + 1) begin : full_adder_loop
    full_adder fa(clock, a_in[i], b_in[i], carry[i], out[i], carry[i+1]);
  end
endgenerate

endmodule

module full_adder(clock, a, b, cin, sum, cout);

input clock;
input a, b, cin;
output sum, cout;

wire s1, c1, c2;

assign s1 = a ^ b;
assign sum = s1 ^ cin;
assign c1 = a & b;
assign c2 = s1 & cin;
assign cout = c1 | c2;

endmodule