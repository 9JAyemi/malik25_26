module concat_module_sva (
  input  logic [15:0] in0,
  input  logic [15:0] in1,
  input  logic [31:0] y,
  input  logic        clk,
  input  logic        ce,
  input  logic        clr
);
  // Clock: clk; Reset: clr (synchronous, active-high). Sequential registered output with CE gating.

  // When clr is asserted, y must be 0 on the next cycle.
  reset_clears_next: assert property (
    @(posedge clk) clr |=> (y == '0)
  );

  // While reset is held (from a previous cycle), y stays 0.
  reset_holds_zero: assert property (
    @(posedge clk) $past(clr) |-> (y == '0)
  );

  // With ce HIGH (and not in reset), y loads {in0,in1} on the next cycle.
  load_on_ce: assert property (
    @(posedge clk) disable iff (clr) ce |=> (y == {$past(in0), $past(in1)})
  );

  // With ce LOW (and not in reset), y holds its value on the next cycle.
  hold_when_ce_low: assert property (
    @(posedge clk) disable iff (clr) !ce |=> (y == $past(y))
  );

  // Core next-state relation when not in or just after reset.
  update_main_relation: assert property (
    @(posedge clk) disable iff (clr || $past(clr))
      1'b1 |-> (y == ($past(ce) ? {$past(in0), $past(in1)} : $past(y)))
  );

  // Upper half of y matches in0 on a load.
  upper_half_on_load: assert property (
    @(posedge clk) disable iff (clr) ce |=> (y[31:16] == $past(in0))
  );

  // Lower half of y matches in1 on a load.
  lower_half_on_load: assert property (
    @(posedge clk) disable iff (clr) ce |=> (y[15:0] == $past(in1))
  );

  // Any y change (not around reset) must be caused by ce in the previous cycle.
  y_change_implies_past_ce: assert property (
    @(posedge clk) disable iff (clr || $past(clr)) $changed(y) |-> $past(ce)
  );

endmodule