
module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4 ( CLK, EN, TE, ENCLK );
  input CLK, EN, TE;
  output ENCLK;

  reg ENCLK_reg;
  wire D;

  // D flip-flop
  always @(posedge CLK) begin
    if (EN) begin
      ENCLK_reg <= TE;
    end else begin
      ENCLK_reg <= 0;
    end
  end

  assign ENCLK = ENCLK_reg;

endmodule