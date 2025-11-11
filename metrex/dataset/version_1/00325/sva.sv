// SVA for ddr_clkout
// Focused, concise checks and coverage of key behaviors

module ddr_clkout_sva (
  input logic        clk,
  input logic        pad,
  input logic        sync_clk,
  input logic [7:0]  count,
  input logic        clk_out,
  input logic        d,
  input logic        sync_d1,
  input logic        sync_d2
);

  // sync_clk must toggle every clk rising edge (divide-by-2 of clk)
  assert property (@(posedge clk) !$isunknown($past(sync_clk)) |-> sync_clk == ~$past(sync_clk));

  // "synchronizer" stages behavior
  // Stage 1 samples clk itself: on posedge clk, sampled value must be 1
  assert property (@(posedge clk) sync_d1 === 1'b1);
  // Stage 2 captures sync_d1 on next sync_clk edge
  assert property (@(posedge sync_clk) 1 |=> (sync_d2 === $past(sync_d1)));

  // Counter behavior on sync_clk
  assert property (@(posedge sync_clk)
                   !$isunknown($past(count)) |->
                   (count == (($past(count) == 8'hFF) ? 8'h00 : ($past(count)+8'h01))));

  // clk_out must mirror count[6]
  assert property (@(posedge sync_clk) clk_out === count[6]);

  // d toggles on every clk_out posedge
  assert property (@(posedge clk_out) !$isunknown($past(d)) |-> d == ~$past(d));

  // d only changes when clk_out rises (no spurious toggles)
  assert property (@(posedge sync_clk) $changed(d) |-> $rose(clk_out));

  // pad must equal d at all times (4-state check)
  assert property (@(posedge sync_clk) pad === d);

  // Coverage
  cover property (@(posedge clk)      $rose(sync_clk));
  cover property (@(posedge sync_clk) ($past(count)==8'hFF && count==8'h00)); // wrap
  cover property (@(posedge sync_clk) $rose(clk_out));
  cover property (@(posedge sync_clk) $fell(clk_out));
  cover property (@(posedge sync_clk) $changed(pad));

endmodule

// Bind SVA to DUT
bind ddr_clkout ddr_clkout_sva i_ddr_clkout_sva (
  .clk      (clk),
  .pad      (pad),
  .sync_clk (sync_clk),
  .count    (count),
  .clk_out  (clk_out),
  .d        (d),
  .sync_d1  (sync_d1),
  .sync_d2  (sync_d2)
);