// SVA for ripple_carry_adder
// Bind this file with the DUT to check and cover key behaviors concisely.

module ripple_carry_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] sum,
  input  logic       carry_out,
  input  logic [3:0] carry   // internal reg from DUT
);

  // Sample on any relevant edge to observe combinational behavior and events
  default clocking cb @(
      posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
      posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
      posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
      posedge carry[0] or negedge carry[0] or posedge carry[1] or negedge carry[1] or
      posedge carry[2] or negedge carry[2] or posedge carry[3] or negedge carry[3] or
      posedge carry_out or negedge carry_out
  ); endclocking

  // Arithmetic correctness (only when all operands are known)
  assert property ( !$isunknown({A,B,carry}) |-> {carry_out, sum} == A + B + carry )
    else $error("Adder mismatch: {carry_out,sum} != A + B + carry");

  // Outputs must not go X/Z when inputs/internal are known
  assert property ( !$isunknown({A,B,carry}) |-> !$isunknown({sum,carry_out}) )
    else $error("Unknown on outputs with known inputs");

  // carry register must update to 0001 on carry_out posedge (width-mismatch effect)
  assert property ( @(posedge carry_out) ##0 carry == 4'b0001 )
    else $error("carry not updated to 0001 on carry_out posedge");

  // carry may only change coincident with a carry_out posedge
  assert property (
      disable iff ($isunknown(carry_out))
      @(posedge carry[0] or negedge carry[0] or posedge carry[1] or negedge carry[1] or
        posedge carry[2] or negedge carry[2] or posedge carry[3] or negedge carry[3])
      $rose(carry_out)
  ) else $error("carry changed without carry_out posedge");

  // No zero-time glitches on carry_out
  assert property (
      disable iff ($isunknown(carry_out))
      not ( $changed(carry_out) ##0 $changed(carry_out) )
  ) else $error("carry_out glitches within a delta");

  // Upper carry bits must remain 0 whenever carry is known (due to 1->4 widening)
  assert property ( !$isunknown(carry) |-> carry[3:1] == 3'b000 )
    else $error("carry[3:1] not zero when carry is known");

  // Minimal functional coverage
  cover property ( carry_out );                      // carry generated at least once
  cover property ( {A,B} == 8'h00 );                 // both operands zero
  cover property ( {A,B} == 8'hFF );                 // both operands max
  cover property ( A == 4'hF && B == 4'h1 );         // overflow into carry_out
  cover property ( sum == 4'h0 && carry_out );       // wraparound to zero with carry
  cover property ( sum == 4'hF && !carry_out );      // max sum without carry
endmodule

// Bind into the DUT
bind ripple_carry_adder ripple_carry_adder_sva sva_i (
  .A(A), .B(B), .sum(sum), .carry_out(carry_out), .carry(carry)
);