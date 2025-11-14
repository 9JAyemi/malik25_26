// SVA for sequencDetector: concise, high-quality checks and coverage

module sequencDetector_sva (
  input logic        clock,
  input logic        reset,
  input logic        in,
  input logic        out,
  input logic [2:0]  state
);
  // Mirror state encodings
  localparam logic [2:0] s0=3'b000, s1=3'b001, s2=3'b010, s3=3'b011, s4=3'b100, s5=3'b101;

  // Basic X checks
  a_no_x_inputs:    assert property (@(posedge clock)                      !$isunknown({in,reset}));
  a_no_x_state_out: assert property (@(posedge clock) disable iff (reset)  !$isunknown({state,out}));

  // Synchronous reset behavior
  a_sync_reset: assert property (@(posedge clock) reset |=> (state==s0 && out==1'b0));

  // State legality (default case should never be needed)
  a_state_legal: assert property (@(posedge clock) state inside {s0,s1,s2,s3,s4,s5});

  // Next-state function (golden reference)
  a_next_state: assert property (@(posedge clock) disable iff (reset)
    state ==
      ( ($past(state)==s0) ? ($past(in) ? s1 : s0) :
        ($past(state)==s1) ? ($past(in) ? s1 : s2) :
        ($past(state)==s2) ? ($past(in) ? s1 : s3) :
        ($past(state)==s3) ? ($past(in) ? s1 : s4) :
        ($past(state)==s4) ? ($past(in) ? s5 : s0) :
        ($past(state)==s5) ? ($past(in) ? s1 : s2) :
        s0 ) );

  // Output decode and pulse width
  a_out_decode: assert property (@(posedge clock) disable iff (reset)
    out == (($past(state)==s4 && $past(in)) ? 1'b1 : 1'b0));

  a_out_one_shot: assert property (@(posedge clock) disable iff (reset) out |=> !out);

  // Spec-level equivalence to input stream (10001)
  a_no_false_positive: assert property (@(posedge clock) disable iff (reset)
    out |-> $past(!reset,4) && in && !$past(in,1) && !$past(in,2) && !$past(in,3) && $past(in,4));

  sequence pat10001;
    in ##1 !in ##1 !in ##1 !in ##1 in;
  endsequence
  a_detect_on_pattern: assert property (@(posedge clock) disable iff (reset) pat10001 |=> out);

  // Coverage
  c_seen_detection: cover property (@(posedge clock) pat10001 |=> out);

  // Visit each state
  c_s0: cover property (@(posedge clock) state==s0);
  c_s1: cover property (@(posedge clock) state==s1);
  c_s2: cover property (@(posedge clock) state==s2);
  c_s3: cover property (@(posedge clock) state==s3);
  c_s4: cover property (@(posedge clock) state==s4);
  c_s5: cover property (@(posedge clock) state==s5);

  // Exercise both inputs in each state (transition coverage)
  c_s0_i0: cover property (@(posedge clock) state==s0 && !in);
  c_s0_i1: cover property (@(posedge clock) state==s0 &&  in);
  c_s1_i0: cover property (@(posedge clock) state==s1 && !in);
  c_s1_i1: cover property (@(posedge clock) state==s1 &&  in);
  c_s2_i0: cover property (@(posedge clock) state==s2 && !in);
  c_s2_i1: cover property (@(posedge clock) state==s2 &&  in);
  c_s3_i0: cover property (@(posedge clock) state==s3 && !in);
  c_s3_i1: cover property (@(posedge clock) state==s3 &&  in);
  c_s4_i0: cover property (@(posedge clock) state==s4 && !in);
  c_s4_i1: cover property (@(posedge clock) state==s4 &&  in);
  c_s5_i0: cover property (@(posedge clock) state==s5 && !in);
  c_s5_i1: cover property (@(posedge clock) state==s5 &&  in);
endmodule

bind sequencDetector sequencDetector_sva sva (.*);