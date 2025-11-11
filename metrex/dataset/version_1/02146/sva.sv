// SVA for ripple_carry_adder
// Focused, concise checks + essential coverage. Uses $global_clock for combinational sampling.

module ripple_carry_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] S,
  input  logic       overflow
);

  default clocking cb @ (posedge $global_clock); endclocking

  // Functional equivalence: 5-bit sum must match concatenated outputs when inputs are known
  assert property ( (!$isunknown({A,B})) |-> ({overflow,S} == ({1'b0,A} + {1'b0,B})) )
    else $error("Adder result mismatch: {overflow,S} != A+B");

  // X-propagation sanity: known inputs must produce known outputs
  assert property ( (!$isunknown({A,B})) |-> (!$isunknown({S,overflow})) )
    else $error("Unknown on outputs with known inputs");

  // Pure combinational behavior: if inputs are stable, outputs must stay stable
  assert property ( $stable({A,B}) |-> $stable({S,overflow}) )
    else $error("Outputs changed without input change");

  // Coverage: basic no-overflow and overflow scenarios + corner
  cover property ( (!$isunknown({A,B})) && !overflow );                // no overflow seen
  cover property ( (!$isunknown({A,B})) &&  overflow );                // overflow seen
  cover property ( A==4'h0 && B==4'h0 && S==4'h0 && !overflow );       // zero + zero
  cover property ( {overflow,S} == 5'h10 );                            // exact 16 (carry-only)

endmodule

bind ripple_carry_adder ripple_carry_adder_sva sva_i (
  .A(A), .B(B), .S(S), .overflow(overflow)
);