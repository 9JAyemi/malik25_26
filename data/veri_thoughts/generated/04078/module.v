module MX2X4A12TR (A, B, S0, Y);
  input A, B, S0;
  output Y;
  wire B_not, A_and_B, A_and_B_not;

  not (B_not, B);
  and (A_and_B, A, B);
  and (A_and_B_not, A, B_not);

  assign Y = S0 ? A_and_B_not : A_and_B;
endmodule