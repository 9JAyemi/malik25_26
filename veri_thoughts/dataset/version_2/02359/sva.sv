module counter_sva (
  input logic clk,
  input logic ce,
  input logic clr,
  input logic [7:0] count
);

  // Synchronous clear drives count to zero on that clock.
  sync_clear_zero: assert property (
    @(posedge clk) clr |=> (count == 8'h00)
  );

  // With enable and no clear (prev cycle not in clear), count increments by 1.
  inc_on_ce: assert property (
    @(posedge clk) disable iff (clr)
      (ce && $past(!clr)) |=> (count == $past(count) + 8'd1)
  );

  // With ce low and no clear (prev cycle not in clear), count holds.
  hold_when_ce_low: assert property (
    @(posedge clk) disable iff (clr)
      (!ce && $past(!clr)) |=> (count == $past(count))
  );

  // clr dominates ce when both are high.
  clr_priority_over_ce: assert property (
    @(posedge clk) (clr && ce) |=> (count == 8'h00)
  );

  // With enable and no clear, 0xFF rolls over to 0x00.
  rollover_ff_to_00: assert property (
    @(posedge clk) disable iff (clr)
      (ce && ($past(count) == 8'hFF) && $past(!clr)) |=> (count == 8'h00)
  );

  // Two consecutive enables (no clear) produce a net +2 increment.
  two_cycle_increment: assert property (
    @(posedge clk) disable iff (clr)
      (ce && $past(ce) && $past(!clr) && $past(!clr,2)) |=> (count == $past(count,2) + 8'd2)
  );

  // Two consecutive cycles with ce low (no clear) hold count over 2 cycles.
  hold_two_cycles_no_enable: assert property (
    @(posedge clk) disable iff (clr)
      (!ce && $past(!ce) && $past(!clr) && $past(!clr,2)) |=> (count == $past(count,2))
  );

  // Any change in count must be caused by clr or ce.
  change_implies_cause: assert property (
    @(posedge clk) $changed(count) |=> (clr || ce)
  );

endmodule