// SVA for clk_divider
// Focused, high-quality checks on reset behavior, counter sequencing, and toggle correctness.
// Bindable to the DUT; references internal 'counter'.

`ifndef DISABLE_SVA
module clk_divider_sva (
  input logic        reset,
  input logic        in_clk,
  input logic        out_clk,
  input logic [7:0]  ratio,
  input logic [7:0]  counter
);

  default clocking cb @(posedge in_clk); endclocking

  // Assumptions: constrain to legal ratios (avoid degenerate 0/1)
  assume property (!reset |-> ratio >= 8'd2);

  // While reset asserted, outputs are held low and stable
  assert property (reset |-> (out_clk == 1'b0 && counter == 8'd0
                              && $stable(out_clk) && $stable(counter)));

  // First active edge after reset deassert: out_clk toggles high, counter reloads as expected
  assert property (!reset && $past(reset) |-> (out_clk == 1'b1
                                               && counter == ($past(ratio[7:1]) - 8'd1)));

  // Toggle iff previous counter was zero
  assert property (!reset && $past(!reset) && ($past(counter) == 8'd0) |-> $changed(out_clk));
  assert property (!reset && $past(!reset) && ($past(counter) != 8'd0) |-> !$changed(out_clk));

  // Counter next-state: decrement when nonzero
  assert property (!reset && $past(!reset) && ($past(counter) > 8'd0)
                  |-> counter == $past(counter) - 8'd1);

  // Counter next-state: reload when zero (matches RTL formula; uses pre-toggle out_clk)
  assert property (!reset && $past(!reset) && ($past(counter) == 8'd0)
                  |-> counter == ($past(ratio[7:1]) + ($past(ratio[0]) & $past(out_clk)) - 8'd1));

  // Basic coverage
  cover property (!reset && ratio[0] == 1'b0 && $rose(out_clk) ##[1:255] $fell(out_clk));
  cover property (!reset && ratio[0] == 1'b1 && $rose(out_clk) ##[1:255] $fell(out_clk) ##[1:255] $rose(out_clk));
  cover property (!reset && ratio == 8'd2 && $rose(out_clk) ##1 $fell(out_clk));

endmodule

bind clk_divider clk_divider_sva sva_i (.*);
`endif