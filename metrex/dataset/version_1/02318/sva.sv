// SVA for the given DUTs (focus on concise, high-quality checks and coverage)

// Bind into 'top'
bind top top_sva();
module top_sva;
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Basic wiring correctness
  assert property ($signed(c) == $signed(reg_tmp_c));

  // No X on output after first cycle
  assert property (past_valid |-> !$isunknown(c));

  // Reset behavior and MAC recurrence
  // set high -> next c==0
  assert property (past_valid && $past(set) |-> $signed(c) == 0);
  // set low -> next c == past(c) + past(a*b) (signed, width A+B)
  assert property (past_valid && !$past(set) |-> 
                   $signed(c) == $signed($past(c)) + ($signed($past(a)) * $signed($past(b))));

  // While set remains asserted, c remains 0
  assert property (past_valid && set && $past(set) |-> $signed(c) == 0);

  // Targeted functional coverage
  cover property (past_valid && $past(set) && (c==0));
  cover property (past_valid && !$past(set) &&
                  ($signed($past(a)) * $signed($past(b))) != 0);
  cover property (past_valid && !$past(set) &&
                  ($signed($past(a))<0) && ($signed($past(b))<0));
  cover property (past_valid && !$past(set) &&
                  ($signed($past(a))<0) && ($signed($past(b))>=0));
  // Cover a wrap/overflow event on accumulate (positive product causes wrap)
  cover property (past_valid && !$past(set) &&
                  (($signed($past(a)) * $signed($past(b))) > 0) &&
                  ($signed($past(c)) > $signed($past(c) + ($signed($past(a)) * $signed($past(b))))));
endmodule


// Bind into 'top2'
bind top2 top2_sva();
module top2_sva;
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Basic wiring correctness
  assert property ($signed(c) == $signed(reg_tmp_c));

  // No X on key state after first cycle
  assert property (past_valid |-> !$isunknown({c,reg_a,reg_b}));

  // Hold behavior: hold=1 -> state holds, c holds
  assert property (past_valid && $past(hold) |-> 
                   $stable(reg_a) && $stable(reg_b) &&
                   $signed(c) == $signed($past(c)));

  // Capture behavior: hold=0 -> reg_a/b load from inputs
  assert property (past_valid && $past(!hold) |-> 
                   (reg_a == $past(a)) && (reg_b == $past(b)));

  // MAC recurrence uses previous reg_a/reg_b and past c
  assert property (past_valid && $past(!hold) |-> 
                   $signed(c) == $signed($past(c)) + 
                                  ($signed($past(reg_a)) * $signed($past(reg_b))));

  // Targeted functional coverage
  // Exercise hold toggle and capture
  cover property (past_valid && hold ##1 !hold ##1 hold);
  // Non-zero multiply used in accumulate step
  cover property (past_valid && $past(!hold) &&
                  ($signed($past(reg_a)) * $signed($past(reg_b))) != 0);
  // Negative*negative and negative*positive cases sampled into regs
  cover property (past_valid && $past(!hold) &&
                  ($signed($past(reg_a))<0) && ($signed($past(reg_b))<0));
  cover property (past_valid && $past(!hold) &&
                  ($signed($past(reg_a))<0) && ($signed($past(reg_b))>=0));
endmodule