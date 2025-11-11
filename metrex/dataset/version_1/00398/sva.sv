// SVA for top_module and submodules (concise, quality-focused)
bind top_module top_module_sva i_top_module_sva();

module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // Structural connectivity
  a_conn_sr_out:  assert property (shift_reg_out == shift_reg.data_out);
  a_conn_cnt_out: assert property (counter_out   == counter.data_out);
  a_conn_sum_out: assert property (output_sum    == shift_reg_counter_sum);
  a_conn_sr_en:   assert property (shift_reg.shift_en == !up_down);
  a_conn_sr_load: assert property (shift_reg.load     == data_in);
  a_conn_cnt_ud:  assert property (counter.up_down    == up_down);

  // Reset behavior
  a_sr_reset:     assert property (rst |=> shift_reg.data_out == 8'h00);
  a_cnt_reset:    assert property (rst |=> counter.data_out   == 4'h0);
  a_sum_reset:    assert property (rst |=> output_sum         == 8'h00);

  // Shift-register functional behavior
  a_sr_shift:     assert property (disable iff (rst)
                                   !up_down |=> shift_reg.data_out == { $past(shift_reg.data_out)[6:0], 1'b0 });
  a_sr_load:      assert property (disable iff (rst)
                                   up_down  |=> shift_reg.data_out == $past(data_in));

  // Counter functional behavior (4-bit modulo arithmetic)
  a_cnt_up:       assert property (disable iff (rst)
                                   up_down  |=> counter.data_out == $past(counter.data_out) + 1);
  a_cnt_down:     assert property (disable iff (rst)
                                   !up_down |=> counter.data_out == $past(counter.data_out) - 1);

  // Sum correctness (combinational)
  a_sum_eq:       assert property (output_sum == shift_reg.data_out + counter.data_out);

  // No X/Z on key outputs after reset deasserted
  a_no_x:         assert property (disable iff (rst)
                                   !$isunknown({shift_reg.data_out, counter.data_out, output_sum}));

  // Functional coverage
  c_sr_shift:     cover property (disable iff (rst)
                                   !up_down ##1 shift_reg.data_out == { $past(shift_reg.data_out)[6:0], 1'b0 });
  c_sr_load:      cover property (disable iff (rst)
                                   up_down  ##1 shift_reg.data_out == $past(data_in));
  c_cnt_wrap_up:  cover property (disable iff (rst)
                                   $past(counter.data_out)==4'hF && up_down  ##1 counter.data_out==4'h0);
  c_cnt_wrap_dn:  cover property (disable iff (rst)
                                   $past(counter.data_out)==4'h0 && !up_down ##1 counter.data_out==4'hF);
  c_sum_carry:    cover property (disable iff (rst)
                                   (shift_reg.data_out + counter.data_out) < shift_reg.data_out);
endmodule