
module and2 (
  output Q,
  input A,
  input B
);

  wire invA, invB, nandOut;

  // Instantiate the inv module twice
  inv inv1 (.Q(invA), .A(A));
  inv inv2 (.Q(invB), .A(B));

  // Instantiate the nand2 module
  nand nand1 (.Q(nandOut), .A(invA), .B(invB));

  // Assign the output
  assign Q = ~nandOut;

endmodule
module inv (
  output Q,
  input A
);

  assign Q = ~A;

endmodule
module nand2 (
  output Q,
  input A,
  input B
);

  assign Q = ~(A & B);

endmodule