// SVA for module fsm
// Bind this checker to the DUT to verify reset, state/output correctness,
// next-state function, and provide compact coverage.

module fsm_sva
  #(parameter logic [1:0] State0 = 2'b00,
                         State1 = 2'b01,
                         State2 = 2'b10,
                         State3 = 2'b11)
  (input logic        X,
   input logic        RESET,
   input logic        CLOCK,
   input logic        Z,
   input logic [1:0]  CurrentState,
   input logic [1:0]  NextState);

  default clocking cb @(posedge CLOCK); endclocking
  default disable iff (RESET);

  // Basic sanity
  ap_no_x_state:  assert property ( !$isunknown(CurrentState) );
  ap_no_x_out:    assert property ( !$isunknown(Z) );
  ap_no_x_ns:     assert property ( (!$isunknown({CurrentState,X})) |-> !$isunknown(NextState) );

  // Reset behavior (sync and async)
  ap_sync_reset:  assert property (@(posedge CLOCK) RESET |-> CurrentState == State0);
  ap_async_reset: assert property (@(posedge RESET) CurrentState == State0);

  // Output function: Z is 1 iff in State0
  ap_z_by_state:  assert property ( Z == (CurrentState == State0) );

  // Combinational next-state function correctness
  ap_ns_s01:      assert property ( (CurrentState inside {State0,State1}) |-> (NextState == (X ? State0 : State1)) );
  ap_ns_s3:       assert property ( (CurrentState == State3)             |-> (NextState == (X ? State2 : State1)) );
  ap_ns_s2:       assert property ( (CurrentState == State2)             |-> (NextState == State2) );

  // Registered update matches combinational NextState (when not in reset)
  ap_reg_update:  assert property ( !$past(RESET) |-> (CurrentState == $past(NextState)) );

  // State3 is unreachable during normal operation (no transition targets it)
  ap_no_state3:   assert property ( CurrentState != State3 );

  // Minimal but meaningful coverage
  cp_hit_s0:      cover property ( CurrentState == State0 );
  cp_hit_s1:      cover property ( CurrentState == State1 );
  cp_hit_s2:      cover property ( CurrentState == State2 );
  cp_hit_s3:      cover property ( CurrentState == State3 ); // should remain 0 (unreachable)

  cp_s0_to_s1:    cover property ( (CurrentState == State0 && X == 1'b0) ##1 (CurrentState == State1) );
  cp_s1_to_s0:    cover property ( (CurrentState == State1 && X == 1'b1) ##1 (CurrentState == State0) );
  cp_s2_hold:     cover property ( (CurrentState == State2) ##1 (CurrentState == State2) );
  cp_s3_to_s2:    cover property ( (CurrentState == State3 && X == 1'b1) ##1 (CurrentState == State2) );

  cp_z_high:      cover property ( Z == 1 );
  cp_z_low:       cover property ( Z == 0 );

endmodule

bind fsm fsm_sva #(.State0(State0), .State1(State1), .State2(State2), .State3(State3))
  fsm_sva_i (.X(X), .RESET(RESET), .CLOCK(CLOCK), .Z(Z),
             .CurrentState(CurrentState), .NextState(NextState));