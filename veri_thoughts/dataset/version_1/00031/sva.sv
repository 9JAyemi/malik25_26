// SVA for Mealy: concise, high-quality checks and coverage
// Bind into DUT to observe internal state and verify transition/output logic.

module Mealy_sva (
  input logic        in,
  input logic        out,
  input logic [1:0]  state
);

  // Expected next-state when not in reset (out==1) and on posedge in
  function automatic logic [1:0] f_next_state (input logic [1:0] s);
    unique case (s)
      2'd0: f_next_state = 2'd1; // s0->s1
      2'd1: f_next_state = 2'd3; // s1->s3
      2'd2: f_next_state = 2'd0; // s2->s0
      2'd3: f_next_state = 2'd2; // s3->s2
      default: f_next_state = 2'd0;
    endcase
  endfunction

  // Expected out value (on next cycle) when not in reset (Moore-equivalent at posedge in)
  function automatic logic f_out_from_state (input logic [1:0] s);
    f_out_from_state = (s==2'd1 || s==2'd2); // s1,s2 -> 1; s0,s3 -> 0
  endfunction

  default clocking cb @(posedge in); endclocking

  // Helper: "previous" with history cleared while in reset (!out)
  `define PREV(sig) $past(sig, 1, !out)

  // Sanity: no X when not in reset
  assert property (disable iff (!out) !$isunknown({out, state}));

  // State validity (defensive)
  assert property (disable iff (!out) (state inside {2'd0,2'd1,2'd2,2'd3}));

  // Reset hold behavior on clocks while out==0
  assert property ((!`PREV(out)) |-> (state==2'd0 && out==1'b0));

  // Next-state function when not in reset
  assert property ( (`PREV(out)) |-> (state == f_next_state(`PREV(state))) );

  // Output function when not in reset
  assert property ( (`PREV(out)) |-> (out == f_out_from_state(`PREV(state))) );

  // If out fell since last clock, we must be in reset now and at s0
  assert property ( $fell(out) |-> (out==1'b0 && state==2'd0) );

  // Coverage: hit all states while not in reset
  cover property (disable iff (!out) state==2'd0);
  cover property (disable iff (!out) state==2'd1);
  cover property (disable iff (!out) state==2'd2);
  cover property (disable iff (!out) state==2'd3);

  // Coverage: full 4-state cycle under out==1
  cover property (disable iff (!out)
                  state==2'd0 ##1 state==2'd1 ##1 state==2'd3 ##1 state==2'd2 ##1 state==2'd0);

  // Coverage: observe out edges (if they ever occur)
  cover property (@cb $rose(out));
  cover property (@cb $fell(out));

  `undef PREV
endmodule

// Bind into DUT
bind Mealy Mealy_sva u_mealy_sva (.in(in), .out(out), .state(state));