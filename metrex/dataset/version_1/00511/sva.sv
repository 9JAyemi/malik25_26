// SVA for top_module
module top_module_sva;
  // Bound into top_module scope; can reference internal signals directly
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // State sampling correctness
  a_prev_in:           assert property (disable iff (!past_valid) prev_in == $past(in));
  a_edge_detect_def:   assert property (disable iff (!past_valid) edge_detect == ($past(in[0]) && !in[0]));
  a_pulse_eq_edge:     assert property (disable iff (!past_valid) pulse == edge_detect);
  a_no_spurious_pulse: assert property (disable iff (!past_valid) (!($past(in[0]) && !in[0])) |-> !pulse);
  a_no_back2back:      assert property (disable iff (!past_valid) !(pulse && $past(pulse)));

  // Counter behavior
  a_cnt_stable_no_p:   assert property (disable iff (!past_valid) !pulse |-> $stable(counter));
  a_cnt_inc_on_p:      assert property (disable iff (!past_valid)
                                        pulse |=> counter == (($past(counter)==4'd15) ? 4'd0 : $past(counter)+1));
  a_q_matches_cnt:     assert property (q == counter);

  // Coverage
  c_pulse_seen:        cover  property (disable iff (!past_valid) pulse);
  c_wrap_seen:         cover  property (disable iff (!past_valid) (counter==4'd15 && pulse) |=> (counter==4'd0));
  c_two_pulses:        cover  property (disable iff (!past_valid) pulse ##[1:$] pulse);
endmodule

bind top_module top_module_sva sva_inst();