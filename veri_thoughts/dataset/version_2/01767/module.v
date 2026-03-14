
module p_aoi22 (q, qbar, i0, i1, i2, i3);
  output q, qbar;
  input i0, i1, i2, i3;
  wire [1:0] int_0n;

  nor I0 (int_0n[0], i0, i1);
  and I1 (int_0n[1], i2, i3);
  nand I2 (q, int_0n[0], int_0n[1]);
  nor I3 (qbar, int_0n[0], q);
endmodule