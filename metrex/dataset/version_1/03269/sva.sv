// SVA for up_down_counter_bcd
// Bind into DUT to access internals (e.g., BCD_count)

module up_down_counter_bcd_sva;

  // Use DUT scope signals directly via bind
  // signals: Up, Down, Clk, reset, Count, BCD1, BCD0, BCD_output, BCD_count

  default clocking cb @(posedge Clk); endclocking
  default disable iff (reset);

  // Basic sanity: no X/Z on key signals after reset
  assert property (!$isunknown({Up, Down, Count, BCD0, BCD1, BCD_output, BCD_count})));

  // Reset behavior
  assert property (@cb reset |-> (Count == 4'd0));

  // Next-state rules (priority Up over Down)
  assert property (@cb Up |-> Count == $past(Count) + 4'd1);
  assert property (@cb (Down && !Up) |-> Count == $past(Count) - 4'd1);
  assert property (@cb (!Up && !Down) |-> Count == $past(Count));
  assert property (@cb (Up && Down) |-> Count == $past(Count) + 4'd1);

  // Wrap coverage
  cover property (@cb (Count == 4'hF && Up) ##1 (Count == 4'h0));
  cover property (@cb (Count == 4'h0 && Down && !Up) ##1 (Count == 4'hF));

  // BCD converter functional checks (as implemented)
  // 1) Output truncation: BCD_output == {BCD0, BCD_count}; ignores BCD1 (bug-catching)
  assert property (@cb BCD_output == {BCD0, BCD_count});

  // 2) BCD comb deps only from Count
  assert property (@cb $changed(BCD_count) |-> $changed(Count));
  assert property (@cb $changed(BCD0)      |-> $changed(Count));
  assert property (@cb $changed(BCD1)      |-> $changed(Count));

  // 3) Changing only BCD1 must not affect BCD_output (since it is truncated)
  assert property (@cb $changed(BCD1) && $stable(BCD0) && $stable(BCD_count) |-> $stable(BCD_output));

  // 4) Mapping checks per case items
  assert property (@cb (Count <= 4'd9)  |-> (BCD_count == Count));
  assert property (@cb (Count == 4'd10) |-> (BCD_count == 4'd1 && BCD1 == 4'd1));
  assert property (@cb (Count == 4'd11) |-> (BCD_count == 4'd1 && BCD1 == 4'd1 && BCD0 == 4'd1));
  assert property (@cb (Count == 4'd12) |-> (BCD_count == 4'd1 && BCD0 == 4'd1));
  assert property (@cb (Count == 4'd13) |-> (BCD_count == 4'd2));
  assert property (@cb (Count == 4'd14) |-> (BCD_count == 4'd3));
  assert property (@cb (Count == 4'd15) |-> (BCD_count == 4'd4));

  // Coverage: exercise key behaviors
  cover property (@cb !$past(reset) && Up && !Down);      // increment path
  cover property (@cb !$past(reset) && Down && !Up);      // decrement path
  cover property (@cb Up && Down);                        // priority case
  cover property (@cb (Count==4'd9)  ##1 (Count==4'd10)); // 9->10 transition
  cover property (@cb (Count==4'd10) ##1 (Count==4'd11)); // 10->11 transition

endmodule

bind up_down_counter_bcd up_down_counter_bcd_sva sva_inst();