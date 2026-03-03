// SVA checker for DivFrec
module DivFrec_sva (
  input logic        clk,
  input logic        rst,
  input logic [10:0] div,
  input logic        clkd,
  input logic        clk_1kHz
);
  default clocking cb @(posedge clk); endclocking

  // Reset: outputs forced low while rst is asserted
  assert property (@cb rst |-> (clkd==1'b0 && clk_1kHz==1'b0));

  // All output edges are true toggles
  assert property (@cb disable iff (rst) $changed(clkd)     |-> clkd     == ~$past(clkd));
  assert property (@cb disable iff (rst) $changed(clk_1kHz) |-> clk_1kHz == ~$past(clk_1kHz));

  // Variable divider: distance between successive clkd edges equals div_at_edge + 1
  // Also forbids any earlier extra edge (stable until the next one)
  property p_clkd_interval_matches_div;
    int cnt;
    @(cb) disable iff (rst)
      $changed(clkd), cnt = 0
      |-> ( ! $changed(clkd), cnt = cnt + 1 )[*0:$] ##1
          $changed(clkd) ##0 (cnt + 1 == int'(div) + 1);
  endproperty
  assert property (p_clkd_interval_matches_div);

  // 1 kHz generator: exact 50_000-cycle half-period, no early edges
  assert property (@cb disable iff (rst)
    $changed(clk_1kHz) |-> (! $changed(clk_1kHz))[*49999] ##1 $changed(clk_1kHz));

  // ---------------------------------
  // Minimal functional coverage
  // ---------------------------------
  // See at least one edge on each output
  cover property (@cb disable iff (rst) $changed(clkd));
  cover property (@cb disable iff (rst) $changed(clk_1kHz));

  // Exercise key div values at a clkd edge
  cover property (@cb disable iff (rst) $changed(clkd) && div==11'd0);
  cover property (@cb disable iff (rst) $changed(clkd) && div==11'd1);
  cover property (@cb disable iff (rst) $changed(clkd) && div==11'd2047);

  // div changes between clkd edges (dynamic divisor case)
  cover property (@cb disable iff (rst)
    $changed(clkd) ##[1:$] $changed(div) ##[1:$] $changed(clkd));

endmodule

// Bind into the DUT
bind DivFrec DivFrec_sva sva_i (.*);