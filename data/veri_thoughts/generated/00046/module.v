module o311ai (
  input A1,
  input A2,
  input A3,
  input B1,
  input C1,
  output Y
);

  wire n1, n2, n3;

  and and_gate1(n1, A1, B1);  // AND gate combining A1 and B1
  or  or_gate1(n2, A2, n1);   // OR gate combining A2 and the result of the first AND gate
  not not_gate1(n3, A3);      // NOT gate inverting A3
  and and_gate2(Y, n2, n3, C1); // Final AND gate combining the results of the above gates and C1

endmodule
