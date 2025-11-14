// SVA for FSM: concise, high-quality checks and coverage
// Bind this module to the DUT: bind FSM FSM_sva();

module FSM_sva;

  // Use DUT scope signals/params directly via bind
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate || $isunknown({in, current_state, next_state, out}));

  // Static parameter sanity (fail fast)
  initial begin
    if (n < 4) $error("FSM: parameter n must be >= 4 (in[3] is referenced).");
    if (m != 2) $error("FSM: parameter m must be 2 (out is used as 2 bits).");
    if (s_new != 1) $error("FSM: s_new must be 1; else output concatenation widths are inconsistent.");
  end

  // State register updates correctly on the clock
  assert property (current_state == $past(next_state))
    else $error("FSM: current_state must equal prior-cycle next_state.");

  // No self-loop in the specified transition function (under 2-valued inputs)
  assert property (current_state != next_state)
    else $error("FSM: next_state must differ from current_state.");

  // Next-state function correctness
  assert property (current_state == STATE_A &&  in[0] |-> next_state == STATE_B);
  assert property (current_state == STATE_A && !in[0] |-> next_state == STATE_C);

  assert property (current_state == STATE_B &&  in[1] |-> next_state == STATE_D);
  assert property (current_state == STATE_B && !in[1] |-> next_state == STATE_A);

  assert property (current_state == STATE_C &&  in[2] |-> next_state == STATE_A);
  assert property (current_state == STATE_C && !in[2] |-> next_state == STATE_D);

  assert property (current_state == STATE_D &&  in[3] |-> next_state == STATE_C);
  assert property (current_state == STATE_D && !in[3] |-> next_state == STATE_B);

  // Output decoding correctness (s_new == 1)
  generate if (s_new == 1) begin
    assert property (current_state == STATE_A |-> out == 2'b10);
    assert property (current_state == STATE_B |-> out == 2'b01);
    assert property (current_state == STATE_C |-> out == 2'b11);
    assert property (current_state == STATE_D |-> out == 2'b00);
  end endgenerate

  // Basic X-check on outputs when inputs/state are known
  assert property (!$isunknown(out))
    else $error("FSM: out contains X/Z when inputs/state are known.");

  // Functional coverage: states, transitions, and representative loops
  cover property (current_state == STATE_A);
  cover property (current_state == STATE_B);
  cover property (current_state == STATE_C);
  cover property (current_state == STATE_D);

  cover property ($past(current_state) == STATE_A && current_state == STATE_B);
  cover property ($past(current_state) == STATE_A && current_state == STATE_C);
  cover property ($past(current_state) == STATE_B && current_state == STATE_D);
  cover property ($past(current_state) == STATE_B && current_state == STATE_A);
  cover property ($past(current_state) == STATE_C && current_state == STATE_A);
  cover property ($past(current_state) == STATE_C && current_state == STATE_D);
  cover property ($past(current_state) == STATE_D && current_state == STATE_C);
  cover property ($past(current_state) == STATE_D && current_state == STATE_B);

  // Cover full-state round trips through both decision branches
  cover property (current_state == STATE_A ##1 current_state == STATE_B ##1
                  current_state == STATE_D ##1 current_state == STATE_C ##1
                  current_state == STATE_A);

  cover property (current_state == STATE_A ##1 current_state == STATE_C ##1
                  current_state == STATE_D ##1 current_state == STATE_B ##1
                  current_state == STATE_A);

  // Cover all output codes
  cover property (out == 2'b00);
  cover property (out == 2'b01);
  cover property (out == 2'b10);
  cover property (out == 2'b11);

endmodule

// To attach: bind FSM FSM_sva();