module sky130_fd_sc_ms__xor3 (
  input A,
  input B,
  input C,
  output X
);

  wire wire1;
  wire wire2;
  
  assign wire1 = A ^ B;
  assign wire2 = wire1 ^ C;
  assign X = ~wire2;


endmodule