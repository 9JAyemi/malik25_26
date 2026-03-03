// SVA for my_module: bind these assertions to the DUT

module my_module_assertions;
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Structural/functional correctness
  ap_wire_eq_reg:    assert property (data_wire == data_reg);
  ap_reg_samples_in: assert property (data_reg  == $past(data_in));
  ap_func_correct:   assert property (data_out  == (data_wire <= 4'd5));
  ap_end_to_end:     assert property (data_out  == ($past(data_in) <= 4'd5));

  // Sanity/glitch/X checks
  ap_no_glitch:      assert property ($stable(data_reg) |-> $stable(data_out));
  ax_no_x_out:       assert property (!$isunknown(data_out));
  ax_no_x_int:       assert property (!$isunknown({data_reg, data_wire}));

  // Coverage (branches, boundaries, extremes, transitions)
  cp_true_branch:    cover property ((data_wire <= 4'd5) &&  data_out);
  cp_false_branch:   cover property ((data_wire >  4'd5) && !data_out);
  cp_bound_5:        cover property (data_wire == 4'd5 &&  data_out);
  cp_bound_6:        cover property (data_wire == 4'd6 && !data_out);
  cp_cross_up:       cover property (data_wire == 4'd5 ##1 data_wire == 4'd6);
  cp_cross_down:     cover property (data_wire == 4'd6 ##1 data_wire == 4'd5);
  cp_min:            cover property (data_wire == 4'd0  &&  data_out);
  cp_max:            cover property (data_wire == 4'd15 && !data_out);
  cp_out_toggle:     cover property ($changed(data_out));
endmodule

bind my_module my_module_assertions my_module_assertions_inst();