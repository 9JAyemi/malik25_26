module full_adder (
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule

module ripple_carry_adder #(
  parameter n = 4 // number of bits in the input and output
)(
  input [n-1:0] A,
  input [n-1:0] B,
  output [n-1:0] S
);


wire [n:0] carry;
genvar i;

generate
  for (i = 0; i < n; i = i + 1) begin : adder
    full_adder fa (
      .A(A[i]),
      .B(B[i]),
      .Cin(carry[i]),
      .S(S[i]),
      .Cout(carry[i+1])
    );
  end
endgenerate

assign carry[0] = 1'b0;

endmodule