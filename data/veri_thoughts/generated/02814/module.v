
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W31_0_3 ( CLK, EN, ENCLK, TE );
  input CLK, EN, TE;
  output ENCLK;

  // Replace TBUF with a D-flip-flop
  reg EN_latch;
  always @(posedge CLK) begin
    if (TE) begin
      EN_latch <= EN;
    end
  end

  // Replace BUFX with a buffer
  assign ENCLK = EN_latch;
endmodule
