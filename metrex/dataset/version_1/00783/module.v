
module full_adder (
  input A,
  input B,
  input CIN,
  output SUM,
  output COUT
);

  assign SUM = A ^ B ^ CIN;
  assign COUT = (A & (B | CIN)) | (B & CIN);

endmodule
module four_bit_adder (
  input [3:0] A,
  input [3:0] B,
  output [4:0] SUM
);

  wire CARRY0;
  wire CARRY1;
  wire CARRY2;

  full_adder op1 (A[0], B[0], 0, SUM[0], CARRY0);
  full_adder op2 (A[1], B[1], CARRY0, SUM[1], CARRY1);
  full_adder op3 (A[2], B[2], CARRY1, SUM[2], CARRY2);
  full_adder op4 (A[3], B[3], CARRY2, SUM[3], SUM[4]);

endmodule