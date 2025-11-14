// SVA for frequency_synthesizer
// Bind into the DUT; focuses on next-state and mode-isolation checks plus key coverage.

bind frequency_synthesizer frequency_synthesizer_sva #(.PLL_DIV(pll_div)) sva_inst (.*);

module frequency_synthesizer_sva #(
  parameter logic [15:0] PLL_DIV = 16'd1
)(
  input  logic        ref_clk,
  input  logic        ctrl,
  input  logic [11:0] freq_word,
  input  logic [15:0] phase_acc,
  input  logic [15:0] out,

  // internal DUT state (connected by bind)
  input  logic [15:0] phase_accumulator,
  input  logic [15:0] dds_clk_divider,
  input  logic [15:0] pll_clk_divider,
  input  logic [15:0] out_reg
);

  logic past_valid;
  always_ff @(posedge ref_clk) past_valid <= 1'b1;

  default clocking cb @ (posedge ref_clk); endclocking
  default disable iff (!past_valid);

  // out must mirror out_reg
  assert property (out == out_reg);

  // DDS divider next-state
  assert property (ctrl && (dds_clk_divider != freq_word) |=> dds_clk_divider == $past(dds_clk_divider) + 16'd1);
  assert property (ctrl && (dds_clk_divider == freq_word) |=> dds_clk_divider == 16'd0);
  assert property (!ctrl |=> dds_clk_divider == $past(dds_clk_divider));

  // PLL divider next-state
  assert property (!ctrl && (pll_clk_divider != PLL_DIV) |=> pll_clk_divider == $past(pll_clk_divider) + 16'd1);
  assert property (!ctrl && (pll_clk_divider == PLL_DIV) |=> pll_clk_divider == 16'd0);
  assert property (ctrl |=> pll_clk_divider == $past(pll_clk_divider));

  // out_reg next-state per mode/event
  // DDS mode: update only on hit, using previous phase_accumulator value (nonblocking semantics)
  assert property (ctrl && (dds_clk_divider == freq_word) |=> out_reg == $past(phase_accumulator[15:0]));
  assert property (ctrl && (dds_clk_divider != freq_word) |=> out_reg == $past(out_reg));
  // PLL mode: increment only on hit
  assert property (!ctrl && (pll_clk_divider == PLL_DIV) |=> out_reg == $past(out_reg) + 16'd1);
  assert property (!ctrl && (pll_clk_divider != PLL_DIV) |=> out_reg == $past(out_reg));

  // phase_accumulator next-state
  // DDS mode: increment only on hit; otherwise hold
  assert property (ctrl && (dds_clk_divider == freq_word) |=> phase_accumulator == $past(phase_accumulator) + $past(phase_acc));
  assert property (ctrl && (dds_clk_divider != freq_word) |=> phase_accumulator == $past(phase_accumulator));
  // PLL mode: always hold
  assert property (!ctrl |=> phase_accumulator == $past(phase_accumulator));

  // Coverage
  cover property (ctrl && (dds_clk_divider == freq_word) ##1 (out_reg == $past(phase_accumulator[15:0])));
  cover property (!ctrl && (pll_clk_divider == PLL_DIV) ##1 (out_reg == $past(out_reg) + 16'd1));
  cover property (!ctrl && (pll_clk_divider == PLL_DIV) && ($past(out_reg) == 16'hFFFF) ##1 (out_reg == 16'h0000));
  cover property (ctrl ##1 !ctrl ##1 ctrl); // mode switches both ways

endmodule