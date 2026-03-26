module half_subtractor (
  input A,
  input B,
  output D,
  output Bout
);

  assign D = A ^ B;
  assign Bout = ~A & B;

endmodule


module full_subtractor (
  input A,
  input B,
  input Bin,
  output D,
  output Bout
);

  wire D1, Bout1, D2, Bout2;

  half_subtractor HS1(.A(A), .B(B), .D(D1), .Bout(Bout1));
  half_subtractor HS2(.A(D1), .B(Bin), .D(D), .Bout(Bout2));
  assign Bout = Bout1 | Bout2;

endmodule