
module clock_gate_1 ( // Rename module name
  input CLK, EN, TE,
  output ENCLK
);

  assign ENCLK = EN ? (TE ? CLK : 1'b0) : 1'b1;

endmodule

module clock_gate_2 ( // Rename module name
  input CLK, EN, TE,
  output ENCLK
);

  assign ENCLK = EN ? (TE ? CLK : 1'b0) : 1'b1;

endmodule
