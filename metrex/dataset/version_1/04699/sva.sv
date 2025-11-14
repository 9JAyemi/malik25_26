// SVA for clk_buffer_driver
module clk_buffer_driver_sva (
  input clk_in,
  input en,
  input clk_out,
  input d_ff
);

  default clocking cb @(posedge clk_in or negedge en); endclocking

  // Basic consistency
  a_out_eq_int:    assert property (clk_out == d_ff);
  a_known:         assert property (!$isunknown({en, clk_out, d_ff}));

  // Async clear and hold-low while disabled
  a_async_clear:   assert property (@(negedge en) ##0 (d_ff==0 && clk_out==0));
  a_hold_low_dis:  assert property (!en |-> (d_ff==0 && clk_out==0 && $stable(d_ff) && $stable(clk_out)));

  // Enabled posedge drives 1
  a_set_one:       assert property (@(posedge clk_in) en |-> ##0 (d_ff==1 && clk_out==1));

  // No early high after enabling until the next clk posedge
  a_no_early_high: assert property (@(posedge en) (clk_out==0) until_with $rose(clk_in));

  // Output changes only on legal events
  a_posedge_only_on_clk: assert property (@(posedge clk_out) (en && $rose(clk_in)));
  a_negedge_only_on_en:  assert property (@(negedge clk_out) $fell(en));

  // Simple functional coverage
  c_en_rise:       cover property (@(posedge en) 1);
  c_en_fall:       cover property (@(negedge en) 1);
  c_clk_when_dis:  cover property (@(posedge clk_in) !en && !clk_out);
  c_clk_when_en:   cover property (@(posedge clk_in) en && clk_out);
  c_out_rise:      cover property (@(posedge clk_out) 1);
  c_out_fall:      cover property (@(negedge clk_out) 1);

endmodule

bind clk_buffer_driver clk_buffer_driver_sva u_clk_buffer_driver_sva (
  .clk_in (clk_in),
  .en     (en),
  .clk_out(clk_out),
  .d_ff   (d_ff)
);