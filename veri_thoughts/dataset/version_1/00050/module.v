
module XNOR3HD2X(A, B, C, Z);
  input A, B, C;
  output Z;

  assign Z = ~(A ^ B ^ C);
endmodule

