// SVA for decade_counter
// Focus: concise, high-quality checks + coverage. Bind to DUT to access internals.

module decade_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        pause,
  input  logic        resume,
  input  logic [3:0]  q,
  input  logic [2:0]  state,
  input  logic [3:0]  next_q
);
  default clocking cb @(posedge clk); endclocking

  // Helper: expected next_q from current state (1..8)
  function automatic logic [3:0] exp_next_q(input logic [2:0] s);
    exp_next_q = {1'b0, s} + 4'd1; // 0->1, 1->2, ..., 7->8
  endfunction

  // Basic sanity
  ap_no_x:         assert property (disable iff (reset) !$isunknown({pause,resume,q,state,next_q}));
  ap_q_eq_next_q:  assert property (q == next_q); // combinational mirror checked at clock

  // Reset behavior
  ap_reset_vals:   assert property (reset |-> (state == 3'b000 && q == 4'd0 && next_q == 4'd0));

  // Range of q
  ap_q_range:      assert property (q inside {[4'd0:4'd8]});

  // Pause holds output (and next_q)
  ap_pause_holds:  assert property (disable iff (reset) $past(pause) |-> (q == $past(q) && next_q == $past(next_q)));

  // State update rules
  // When paused and no resume => hold state
  ap_state_hold_on_pause: assert property (disable iff (reset) $past(pause && !resume) |-> (state == $past(state)));

  // Resume always advances state by +1 mod 8 (independent of pause)
  ap_state_adv_on_resume: assert property (disable iff (reset) $past(resume) |-> (state == $past(state) + 3'd1));

  // When not paused, next_q must reflect current state's mapping (1..8),
  // and state must advance by +1 (resume either 0 or 1 yields same effect here)
  ap_flow_when_running: assert property (disable iff (reset)
                                         $past(!pause) |-> (q == exp_next_q($past(state)) &&
                                                            state == $past(state) + 3'd1));

  // Wrap checks
  ap_wrap_state:   assert property (disable iff (reset) $past(state)==3'd7 |-> state==3'd0);
  ap_wrap_q:       assert property (disable iff (reset) $past(!pause && q==4'd8) |-> q==4'd1);

  // Coverage
  cv_all_q:        cover  property (disable iff (reset)
                                    !pause ##1 q==4'd1 ##1 q==4'd2 ##1 q==4'd3 ##1 q==4'd4 ##
                                    1 q==4'd5 ##1 q==4'd6 ##1 q==4'd7 ##1 q==4'd8 ##1 q==4'd1);

  cv_pause_hold:   cover  property (disable iff (reset) $past(pause) && q==$past(q));
  cv_resume_while_paused: cover property (disable iff (reset)
                                          $past(pause && resume) && state==$past(state)+3'd1 && q==$past(q));
  cv_wrap:         cover  property (disable iff (reset) q==4'd8 ##1 !pause ##1 q==4'd1);
endmodule

// Bind into DUT instances (connects internals via .* to match names)
bind decade_counter decade_counter_sva u_decade_counter_sva (.*);