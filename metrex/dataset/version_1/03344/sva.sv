// SVA for cmm_errman_cnt_nfl_en
// Bind into DUT scope to access internals

module cmm_errman_cnt_nfl_en_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Knownness
  a_known_inputs:  assert property (!$isunknown({enable, inc_dec_b, index}));
  a_known_outputs: assert property (!$isunknown(count));

  // Asynchronous reset clears (override default disable)
  a_reset_clears: assert property (disable iff (1'b0)
                                   rst |-> (count==0 && reg_count==0 &&
                                            reg_cnt==0 && reg_extra==0 &&
                                            reg_inc_dec_b==0 && reg_uflow==0));

  // Enable low clears on next cycle
  a_enable_low_clears: assert property (!enable |=> (count==0 && reg_cnt==0 && reg_extra==0));

  // Pipeline/arith alignment
  a_reg_incdec_delay: assert property (reg_inc_dec_b == $past(inc_dec_b));
  a_arith_inc:        assert property ($past(enable) && $past(inc_dec_b)
                                       |-> {reg_extra,reg_cnt} == ($past(cnt) + $past(index)));
  a_arith_dec:        assert property ($past(enable) && !$past(inc_dec_b)
                                       |-> {reg_extra,reg_cnt} == ($past(cnt) - $past(index)));

  // Flow flags correctness and exclusivity
  a_oflow_equiv: assert property (oflow == $past(inc_dec_b & index & cnt));
  a_uflow_equiv: assert property (uflow == $past(~inc_dec_b & index & ~count));
  a_flow_mutex:  assert property (!(oflow && uflow));

  // cnt muxing and count update
  a_cnt_mux:            assert property (cnt == (oflow ? 1'b1 : (uflow ? 1'b0 : reg_cnt)));
  a_count_overflow:     assert property (enable && oflow |-> count==1);
  a_count_underflow:    assert property (enable && uflow |-> count==0);
  a_count_no_flow_path: assert property (enable && !oflow && !uflow |-> count==cnt);

  // No-op when index==0
  a_noop_index0: assert property ($past(enable && index==0) |-> (count==$past(count) && !oflow && !uflow));

  // End-to-end 1-step behavior (functional spec)
  a_inc_no_sat: assert property ($past(enable && inc_dec_b && index && (count==0))
                                 |-> (count==1 && !oflow));
  a_inc_sat:    assert property ($past(enable && inc_dec_b && index && (count==1))
                                 |-> (count==1 && oflow));
  a_dec_no_uf:  assert property ($past(enable && !inc_dec_b && index && (count==1))
                                 |-> (count==0 && !uflow));
  a_dec_uf:     assert property ($past(enable && !inc_dec_b && index && (count==0))
                                 |-> (count==0 && uflow));

  // Coverage
  c_inc_no_sat: cover property (count==0 && enable && inc_dec_b && index ##1 (count==1 && !oflow));
  c_inc_sat:    cover property (count==1 && enable && inc_dec_b && index ##1 (count==1 && oflow));
  c_dec_no_uf:  cover property (count==1 && enable && !inc_dec_b && index ##1 (count==0 && !uflow));
  c_dec_uf:     cover property (count==0 && enable && !inc_dec_b && index ##1 (count==0 && uflow));
  c_noop_idx0:  cover property (enable && !index ##1 (count==$past(count)));
  c_enable_clr: cover property ($fell(enable) ##1 (count==0));

endmodule

bind cmm_errman_cnt_nfl_en cmm_errman_cnt_nfl_en_sva;