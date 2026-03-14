
module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_9 (CLK, EN, TE, ENCLK);
  input CLK, EN, TE;
  output ENCLK;

  reg ENCLK_reg = 1'b0;

  always @(posedge CLK or posedge TE) begin
    if (TE == 1'b0) begin
      if (EN == 1'b1) begin
        ENCLK_reg <= #1 1'b1;
      end else begin
        ENCLK_reg <= #1 1'b0;
      end
    end
  end

  assign ENCLK = ENCLK_reg;

endmodule