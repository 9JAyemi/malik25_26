
module full_adder (
  input A,
  input B,
  input C_in,
  output S,
  output C_out
);

assign S = A ^ B ^ C_in;
assign C_out = (A & B) | (A & C_in) | (B & C_in);

endmodule
module ripple_carry_adder #(
  parameter n = 4 // number of bits in A and B
)(
  input [n-1:0] A,
  input [n-1:0] B,
  output [n:0] C
);

wire [n:0] carry; // carry signals for each bit position

// generate carry signals
genvar i;
generate
  for (i = 0; i < n; i = i + 1) begin : carry_gen
    full_adder fa(
      .A(A[i]),
      .B(B[i]),
      .C_in(carry[i]),
      .S(C[i]),
      .C_out(carry[i+1])
    );
  end
endgenerate

// set carry-in for least significant bit
assign carry[0] = 1'b0;

// assign output
assign C[n] = carry[n];

endmodule