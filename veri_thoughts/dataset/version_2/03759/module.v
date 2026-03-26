
module DLATCH ( E, SE, CK, Q );
  input E, SE, CK;
  output Q;

  reg Q_reg;

  always @(posedge CK)
  begin
    if (E)
      Q_reg <= SE;
  end

  assign Q = Q_reg;
endmodule

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_0 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  wire gated_clk;

  DLATCH latch_instance ( .E(EN), .SE(TE), .CK(CLK), .Q(gated_clk) );

  assign ENCLK = gated_clk & CLK;

endmodule
