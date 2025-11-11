// SVA checker for data_accumulation
// Bind into DUT: binds to each instance and references signals directly
module data_accumulation_sva #(parameter THRESHOLD = 256) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic invariants
  a_reset_values:      assert property (reset |-> accumulator==16'd0 && count==4'd0 && valid_b==1'b0);
  a_dataout_eq_acc:    assert property (data_out == accumulator);
  a_nextacc_comb:      assert property (next_accumulator == accumulator + temp_data);

  // Idle hold (no activity -> all state holds)
  a_idle_hold: assert property ((!valid_a && !(ready_b && valid_b))
                               |=> ready_a==$past(ready_a) && valid_b==$past(valid_b)
                                && accumulator==$past(accumulator) && count==$past(count));

  // Updates on valid_a
  a_cnt_inc_on_valid:  assert property (valid_a |=> count == $past(count) + 4'd1);
  a_tmp_upd_on_valid:  assert property (valid_a |=> temp_data == ({8'b0,$past(data_in)} << ($past(count)*3'd8)));
  a_acc_upd_on_valid:  assert property (valid_a |=> accumulator == $past(accumulator) + $past(temp_data));

  // ready_a behavior driven by count inside valid_a branch
  a_rdy_lo_at_1:       assert property (valid_a && (count==4'd1) |=> ready_a==1'b0);
  a_rdy_hi_at_2:       assert property (valid_a && (count==4'd2) |=> ready_a==1'b1);
  a_rdy_hold_other:    assert property (valid_a && (count!=4'd1) && (count!=4'd2) |=> ready_a==$past(ready_a));

  // valid_b behavior (only asserts under valid_a when accumulator >= THRESHOLD)
  a_vb_rise_only_when_valid: assert property ($rose(valid_b) |-> $past(valid_a) && $past(accumulator) >= THRESHOLD);
  a_vb_set_on_thresh:        assert property (valid_a && (accumulator >= THRESHOLD) |=> valid_b==1'b1);
  a_vb_hold_no_thresh:       assert property (valid_a && (accumulator <  THRESHOLD) |=> valid_b==$past(valid_b));

  // Handshake clear (only when not taking valid_a branch)
  a_hs_clears: assert property (!valid_a && ready_b && valid_b
                               |=> accumulator==16'd0 && count==4'd0 && valid_b==1'b0 && ready_a==1'b1);

  // Coverage
  c_two_bytes_toggle: cover property (valid_a && count==4'd1 ##1 valid_a && count==4'd2 ##1 ready_a);
  c_vb_rise:          cover property ($rose(valid_b));
  c_hs_cycle:         cover property ($rose(valid_b) ##[1:$] (ready_b && valid_b)
                                      ##1 (accumulator==16'd0 && count==4'd0 && !valid_b && ready_a));
  c_thresh_event:     cover property (valid_a && (accumulator >= THRESHOLD));

endmodule

bind data_accumulation data_accumulation_sva #(.THRESHOLD(THRESHOLD)) sva_inst();