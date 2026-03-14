module aoi211hd4x (
  input A,
  input B,
  input C,
  input D,
  input E,
  input F,
  input G,
  input H,
  output Z
);

  wire I0_out, I1_out, I2_out, I3_out, I4_out, I5_out, I6_out, I7_out, I8_out;
  
  and #(2) and1 (I0_out, A, B);
  and #(2) and2 (I1_out, C, D);
  and #(2) and3 (I3_out, E, F);
  and #(2) and4 (I5_out, G, H);
  or #(2) or1 (I2_out, I0_out, I1_out);
  or #(2) or2 (I4_out, I2_out, I3_out);
  or #(2) or3 (I6_out, I4_out, I5_out);
  not #(2) not1 (Z, I6_out);

endmodule