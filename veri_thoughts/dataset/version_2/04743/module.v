module ripple_carry_adder (
  input [n-1:0] a,
  input [n-1:0] b,
  input cin,
  output [n-1:0] s,
  output cout
);

parameter n = 4; // number of bits in input numbers A and B

wire [n:0] carry;
assign carry[0] = cin;

// Full Adder
genvar i;
generate
  for (i = 0; i < n; i = i + 1) begin : full_adder
    assign s[i] = a[i] ^ b[i] ^ carry[i];
    assign carry[i+1] = (a[i] & b[i]) | (a[i] & carry[i]) | (b[i] & carry[i]);
  end
endgenerate

assign cout = carry[n];

endmodule