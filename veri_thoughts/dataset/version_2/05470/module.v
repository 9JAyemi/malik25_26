
module DFF(input D, input CLK, output Q);
  reg Q;
  always @(posedge CLK) Q <= D;
endmodule

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  wire enable;
  assign enable = EN & TE;

  DFF latch ( .D(enable), .CLK(CLK), .Q(ENCLK) );

endmodule
