
module sky130_fd_sc_hd__mux_2 (
  input [3:0] A,
  input [3:0] B,
  input S,
  output [3:0] Y
);

  assign Y = S ? B : A;

endmodule
