// SVA for bcd_counter_and_gate
// Bind into DUT; accesses internal signals (count, bcd_out, and_result)
module bcd_counter_and_gate_sva;

  // Use DUT clock; ignore checks while reset=1 unless noted
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (checked even when reset=1 at the clock)
  a_rst_holds_zero: assert property (@(posedge clk) reset |-> count == 4'b0000);

  // Enables are forced high
  a_ena_const:      assert property (ena == 4'hF);

  // Counter behavior: every bit toggles each cycle (given ena==4'hF)
  a_count_toggles:  assert property (count == ~$past(count));

  // AND gate correctness
  a_and_gate:       assert property (and_result == (a & b));

  // BCD output equals concatenation (>=5 term is effectively 0 for 1-bit digits)
  a_bcd_eq_concat:  assert property (bcd_out == {count[3],count[2],count[1],count[0]});

  // q correctness and width/zero-extension
  a_q_upper_zero:   assert property (q[15:4] == 12'h000);
  a_q_when_and0:    assert property (!and_result |-> (q == 16'h0000));
  a_q_when_and1:    assert property ( and_result |-> (q[3:0] == bcd_out && q[15:4] == 12'h000));

  // Sanity: no X/Z on key signals
  a_no_x:           assert property (!$isunknown({a,b,reset,ena,and_result,bcd_out,count,q}));

  // Functional coverage
  c_count_flip:     cover  property (count==4'h0 ##1 count==4'hF ##1 count==4'h0);
  c_and_toggle:     cover  property (!and_result ##1 and_result ##1 !and_result);
  c_q_nonzero:      cover  property (and_result && q == 16'h000F);

endmodule

bind bcd_counter_and_gate bcd_counter_and_gate_sva sva_inst();