module nand4x1 (Z, A, B, C, D);
  output Z;
  input A, B, C, D;

  wire nand1_out, nand2_out, nand3_out;

  nand  nand1 (nand1_out, A, B);
  nand  nand2 (nand2_out, C, D);
  nand  nand3 (Z, nand1_out, nand2_out, 1);
endmodule