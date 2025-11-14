// SVA for Mealy. Focused, high-signal-coverage, concise checks and covers.
// Bind this to the DUT to access internal state.

module Mealy_sva (
  input  logic       in,
  input  logic       out,
  input  logic [1:0] state
);
  localparam int s0 = 0;
  localparam int s1 = 1;
  localparam int s2 = 2;
  localparam int s3 = 3;

  default clocking cb @(posedge in or negedge out); endclocking

  // Basic sanity
  a_known:     assert property ( !$isunknown({in,out,state}) );
  a_state_rng: assert property ( state inside {s0,s1,s2,s3} );

  // Asynchronous reset via out falling
  a_async_rst_edge: assert property ( $fell(out) |-> (out==1'b0 && state==s0) );
  a_rst_level:      assert property ( (out==1'b0) |-> (state==s0) );

  // Output function on posedge in (previous out==1). This is observed at the next sample.
  // With in=1 at posedge, mapping reduces to: s1|s2 -> out=1, s0|s3 -> out=0
  a_out_map_on_in_pos: assert property (
    $rose(in) && $past(out)
    |=> out == (($past(state)==s1 || $past(state)==s2) ? 1'b1 : 1'b0)
  );

  // Next-state function on posedge in when no reset is induced (i.e., expected out=1)
  a_ns_s1_to_s3: assert property (
    $rose(in) && $past(out) && ($past(state)==s1)
    |=> state==s3
  );
  a_ns_s2_to_s0: assert property (
    $rose(in) && $past(out) && ($past(state)==s2)
    |=> state==s0
  );

  // Posedge in from states that force out=0 must immediately reset next sample
  a_in_pos_forces_reset_from_s0_s3: assert property (
    $rose(in) && $past(out) && ($past(state) inside {s0,s3})
    |=> ($fell(out) && state==s0)
  );

  // Coverage: reach all states
  c_s0: cover property ( state==s0 );
  c_s1: cover property ( state==s1 );
  c_s2: cover property ( state==s2 );
  c_s3: cover property ( state==s3 );

  // Coverage: observe reachable transition/arcs on posedge in
  c_arc_s1_s3: cover property ( $rose(in) && $past(out) && $past(state)==s1 |=> state==s3 );
  c_arc_s2_s0: cover property ( $rose(in) && $past(out) && $past(state)==s2 |=> state==s0 );

  // Coverage: observe reset induced by posedge in from s0/s3
  c_in_pos_resets: cover property (
    $rose(in) && $past(out) && ($past(state) inside {s0,s3})
    |=> ($fell(out) && state==s0)
  );

  // Coverage: see at least one async reset edge
  c_out_fall: cover property ( $fell(out) );

endmodule

// Bind to the DUT (adjust instance/namespace if needed)
bind Mealy Mealy_sva u_mealy_sva (.in(in), .out(out), .state(state));