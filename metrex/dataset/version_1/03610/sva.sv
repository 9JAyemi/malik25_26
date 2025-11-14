// SVA for top_module (quality-focused, concise). Bind this to the DUT.

module top_module_sva (top_module dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst_n)

  // Combinational relations
  a_sum_func:   assert property (dut.sum == {1'b0,dut.data_in_1}+{1'b0,dut.data_in_2});
  a_carry_msb:  assert property (dut.carry == dut.sum[8]);
  a_ready_def:  assert property (dut.ready_a == (!dut.valid_b || dut.ready_b));

  // Sequential mapping
  a_data_out_q: assert property ($past(dut.rst_n) |-> dut.data_out == $past(dut.sum));
  a_valid_b_q:  assert property ($past(dut.rst_n) |-> dut.valid_b  == $past(dut.valid_a));
  a_sum2_accum: assert property ($past(dut.rst_n) |-> dut.sum2     == $past(dut.sum2) + $past(dut.sum));

  // Reset behavior
  a_reset_vals: assert property (!dut.rst_n |-> (dut.data_out==9'd0 && dut.valid_b==1'b0 && dut.sum2==9'd0));
  a_ready_rst:  assert property (!dut.rst_n |-> dut.ready_a==1'b1);

  // No X on key outputs when active
  a_no_x_out:   assert property (!$isunknown({dut.data_out, dut.valid_b, dut.ready_a}));

  // Coverage
  c_rst_release:     cover property ($rose(dut.rst_n));
  c_overflow:        cover property (dut.sum[8]);
  c_no_overflow:     cover property (!dut.sum[8]);
  c_hand_00:         cover property ({dut.valid_a,dut.ready_b}==2'b00);
  c_hand_01:         cover property ({dut.valid_a,dut.ready_b}==2'b01);
  c_hand_10:         cover property ({dut.valid_a,dut.ready_b}==2'b10);
  c_hand_11:         cover property ({dut.valid_a,dut.ready_b}==2'b11);
  c_backpressure_ok: cover property (dut.valid_a && !dut.ready_b ##1 dut.valid_a && !dut.ready_b ##1 dut.ready_b);
  c_accum_wrap:      cover property ($past(dut.rst_n) && (($past(dut.sum2)+$past(dut.sum)) < $past(dut.sum2)));

endmodule

bind top_module top_module_sva sva_top();