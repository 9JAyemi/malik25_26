// SVA for my_module
// Bind this checker: bind my_module my_module_sva svai();

module my_module_sva;

  // Safe use of $past
  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Connectivity and structural invariants
  a_q_path:       assert property (q === q_wire && q_wire === q_reg);
  a_clk_path:     assert property (clk_wire === clk);
  a_dwire_map0:   assert property ((data_en === 1'b0) |-> (d_wire === d));
  a_dwire_map1:   assert property ((data_en === 1'b1) |-> (d_wire === q_wire));

  // Notifier and derived wires
  a_not_wire_0:   assert property (notifier_wire === 1'b0);
  a_den_when_no_not: assert property ((notifier === 1'b0) |-> (data_en_wire === data_en));
  a_den_x_when_not:  assert property ((notifier === 1'b1) |-> $isunknown(data_en_wire));

  // Power pins derived wires (when inputs are known)
  a_vpwr0:        assert property ((vpwr === 1'b0) |-> (vpwr_wire === 1'b1));
  a_vpwr1:        assert property ((vpwr === 1'b1) |-> (vpwr_wire === 1'b1));
  a_vgnd0:        assert property ((vgnd === 1'b0) |-> (vgnd_wire === 1'b0));
  a_vgnd1:        assert property ((vgnd === 1'b1) |-> (vgnd_wire === 1'b1));

  // Functional behavior (sync, priority: reset > set > hold > load)
  a_reset:        assert property (reset            |=> (q == 1'b0));
  a_set:          assert property (!reset &&  set   |=> (q == 1'b1));
  a_rst_over_set: assert property (reset &&   set   |=> (q == 1'b0));
  a_hold:         assert property (!reset && !set &&  data_en |=> (q == $past(q)));
  a_load:         assert property (!reset && !set && !data_en |=> (q == $past(d)));

  // Output changes only on posedge clk
  a_no_negedge_glitch: assert property (@(negedge clk) $stable(q));

  // No X on q when power good and no notifier
  let power_good = (vpwr === 1'b1) && (vgnd === 1'b0) && (notifier === 1'b0);
  a_no_x_when_pgood:   assert property (power_good |-> !$isunknown(q));

  // Coverage: exercise all control paths and effects
  c_reset_path:     cover property (reset ##1 !reset);
  c_set_path:       cover property (!reset && set);
  c_hold_path:      cover property (!reset && !set &&  data_en ##1 $stable(q));
  c_load_path:      cover property (!reset && !set && !data_en ##1 (q == $past(d)));
  c_rst_and_set:    cover property (reset && set);
  c_hold_then_load: cover property (!reset && !set && data_en ##1 !data_en);
  c_q_toggle_on_load: cover property (!reset && !set && !data_en && (d != q) ##1 (q != $past(q)));

endmodule