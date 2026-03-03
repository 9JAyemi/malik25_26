// SVA for my_ff: synchronous clear (SET_B==1) has priority; otherwise Q captures D on each posedge CLK.
// Concise, high-quality checks + focused coverage.

module my_ff_sva (
    input logic D,
    input logic Q,
    input logic SET_B,
    input logic CLK
);
  default clocking cb @ (posedge CLK); endclocking

  // Gate $past() usage
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Inputs must be known at sample time
  a_inputs_known: assert property ( !$isunknown({D, SET_B}) );

  // Q becomes known after first clock
  a_q_known:     assert property ( past_valid |-> !$isunknown(Q) );

  // Functional behavior: synchronous clear dominates; else capture D
  a_func: assert property (
    past_valid |-> Q == ( $past(SET_B) ? 1'b0 : $past(D) )
  );

  // Basic coverage
  // Data captures
  c_cap_0: cover property ( past_valid && !$past(SET_B) && ($past(D)==1'b0) && (Q==1'b0) );
  c_cap_1: cover property ( past_valid && !$past(SET_B) && ($past(D)==1'b1) && (Q==1'b1) );
  // Clear dominates even if D=1
  c_clr_prio: cover property ( past_valid && ($past(SET_B)==1'b1) && ($past(D)==1'b1) && (Q==1'b0) );
  // Q toggles under normal capture (SET_B low)
  c_q_toggle: cover property ( past_valid && !$past(SET_B) && (Q != $past(Q)) );
  // Clear event from Q=1
  c_clr_from1: cover property ( past_valid && ($past(Q)==1'b1) && ($past(SET_B)==1'b1) && (Q==1'b0) );

endmodule

// Bind into DUT
bind my_ff my_ff_sva u_my_ff_sva (.D(D), .Q(Q), .SET_B(SET_B), .CLK(CLK));