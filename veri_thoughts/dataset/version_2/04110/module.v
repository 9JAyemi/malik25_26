module sky130_fd_sc_hd__nor4b (
  input A,
  input B,
  input C,
  input D_N,
  input VPWR,
  input VGND,
  input VPB,
  input VNB,
  output Y
);

  assign Y = ~(A | B | C | D_N);

endmodule