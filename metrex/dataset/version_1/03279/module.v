
module frequency_synthesizer (
  input ref_clk,
  input ctrl,
  input [11:0] freq_word,
  input [15:0] phase_acc,
  output [15:0] out
);

parameter pll_mult = 10;
parameter pll_div = 1;
parameter clk_freq = 50e6;
parameter dds_clk_freq = 100e6;

reg [15:0] phase_accumulator;
reg [15:0] dds_clk_divider;
reg [15:0] pll_clk_divider;
reg [15:0] out_reg;

always @(posedge ref_clk) begin
  if (ctrl) begin // DDS mode
    dds_clk_divider <= dds_clk_divider + 1;
    if (dds_clk_divider == freq_word) begin
      dds_clk_divider <= 0;
      phase_accumulator <= phase_accumulator + phase_acc;
      out_reg <= phase_accumulator[15:0];
    end
  end else begin // PLL mode
    pll_clk_divider <= pll_clk_divider + 1;
    if (pll_clk_divider == pll_div) begin
      pll_clk_divider <= 0;
      out_reg <= out_reg + 1'b1;
    end
  end
end

assign out = out_reg;

endmodule