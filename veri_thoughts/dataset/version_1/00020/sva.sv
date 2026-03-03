// SVA for adder_16bit — bind into the DUT’s scope to check internal wires too.
module adder_16bit_sva;
  // Use a global clock for sampling (most simulators provide $global_clock).
  default clocking cb @(posedge $global_clock); endclocking

  // Core functional correctness: when inputs are known, outputs equal A+B (17-bit).
  a_full_correct: assert property ( !$isunknown({A,B}) |-> {C,S} == A + B );

  // Outputs are known whenever inputs are known.
  a_known_out:    assert property ( !$isunknown({A,B}) |-> !$isunknown({S,C}) );

  // Purely combinational behavior: if inputs don’t change, outputs don’t change.
  a_no_latch:     assert property ( $stable({A,B}) |-> $stable({S,C}) );

  // Internal connectivity/definition checks.
  a_sum_def:      assert property ( sum == {1'b0, A} + {1'b0, B} );
  a_sum_conn:     assert property ( {C,S} == sum );
  a_temp_def:     assert property ( temp == (A ^ B) );

  // Commutativity observed across cycles: swapping A/B preserves {C,S}.
  a_commute_obs:  assert property (
                     !$isunknown({A,B,$past(A),$past(B)}) &&
                     (A == $past(B) && B == $past(A)) |-> {C,S} == $past({C,S})
                   );

  // Coverage: exercise key scenarios.
  c_carry0:   cover property ( !$isunknown({A,B}) && !C );
  c_carry1:   cover property ( !$isunknown({A,B}) &&  C );
  c_zero0:    cover property ( !$isunknown({A,B}) && A==16'h0000 && B==16'h0000 && S==16'h0000 && C==1'b0 );
  c_max_plus1:cover property ( !$isunknown({A,B}) && A==16'hFFFF && B==16'h0001 && S==16'h0000 && C==1'b1 );
  c_wrap:     cover property ( !$isunknown({A,B}) && (A!=0 || B!=0) && S==16'h0000 );
  c_id0A:     cover property ( !$isunknown({A,B}) && A==16'h0000 );
  c_id0B:     cover property ( !$isunknown({A,B}) && B==16'h0000 );
  c_maxmax:   cover property ( !$isunknown({A,B}) && A==16'hFFFF && B==16'hFFFF && C==1'b1 );
endmodule

bind adder_16bit adder_16bit_sva sva_i();