
module Half_Subtractor (
  input A, B,
  output D, Bout
);

  assign D = A ^ B;
  assign Bout = A < B;

endmodule
module Full_Subtractor (
  input A, B, Bin,
  output D, Bout
);

  wire D1, Bout1;
  Half_Subtractor HS1 (.A(A), .B(B), .D(D1), .Bout(Bout1));
  Half_Subtractor HS2 (.A(D1), .B(Bin), .D(D), .Bout()); //Bout is not assigned here

  assign Bout = Bout1 | (Bin & (A <= B));

endmodule