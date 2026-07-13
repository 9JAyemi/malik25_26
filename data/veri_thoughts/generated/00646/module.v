
module carry_select_adder_32bit (A, B, Cin, S);
  input [31:0] A;
  input [31:0] B;
  input Cin;
  output [31:0] S;

  // Generate the sum and carry for each bit
  wire [31:0] sum, carry;
  genvar i;
  generate
    for (i = 0; i < 32; i = i + 1) begin: full_adder_instances
      full_adder fa (
        .A(A[i]),
        .B(B[i]),
        .Cin(Cin),
        .S(sum[i]),
        .Cout(carry[i])
      );
    end
  endgenerate

  // Select the correct sum and carry based on the input carry
  assign S = Cin ? sum : carry;

endmodule

module full_adder (A, B, Cin, S, Cout);
  input A, B, Cin;
  output S, Cout;

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (A & Cin) | (B & Cin);
endmodule
