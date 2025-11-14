// SVA for mux4to1. Bind this module to the DUT and drive clk from TB.
// Focus: functional correctness, structure consistency, X/knownness, and coverage.

module mux4to1_sva #(
  parameter bit CHECK_INTERNAL = 1
)(
  input  logic clk,

  // DUT pins
  input  logic A, B, C, D,
  input  logic S0, S1,
  input  logic Y,

  // DUT internals (optional; connect only if CHECK_INTERNAL=1)
  input  logic not_S0_out,
  input  logic not_S1_out,
  input  logic and1_out,
  input  logic and2_out,
  input  logic and3_out,
  input  logic and4_out
);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness (with select lines known)
  property p_mux_func;
    !$isunknown({S0,S1}) |-> (Y === (S1 ? (S0 ? D : B) : (S0 ? C : A)));
  endproperty
  assert property (p_mux_func);

  // Y must be known if all drivers/selects are known
  assert property ( !$isunknown({S0,S1,A,B,C,D}) |-> !$isunknown(Y) );

  // Internal structure checks (optional)
  if (CHECK_INTERNAL) begin
    // Inverters
    assert property ( not_S0_out === ~S0 );
    assert property ( not_S1_out === ~S1 );

    // AND terms
    assert property ( and1_out === (A & ~S0 & ~S1) );
    assert property ( and2_out === (B & ~S0 &  S1) );
    assert property ( and3_out === (C &  S0 & ~S1) );
    assert property ( and4_out === (D &  S0 &  S1) );

    // OR composition
    assert property ( Y === (and1_out | and2_out | and3_out | and4_out) );

    // Only one product term can be 1 for known selects (zero- or one-hot)
    assert property ( !$isunknown({S0,S1}) |-> $onehot0({and1_out,and2_out,and3_out,and4_out}) );
  end

  // Coverage: see all select combinations mapping to Y, and both Y edges
  cover property ( (S1==0 && S0==0) && (Y === A) );
  cover property ( (S1==1 && S0==0) && (Y === B) );
  cover property ( (S1==0 && S0==1) && (Y === C) );
  cover property ( (S1==1 && S0==1) && (Y === D) );
  cover property ( Y ##1 !Y );
  cover property ( !Y ##1 Y );

endmodule

// Example bind (adjust clk path to your TB)
// bind mux4to1 mux4to1_sva #(.CHECK_INTERNAL(1)) i_mux4to1_sva (
//   .clk(tb.clk),
//   .A(A), .B(B), .C(C), .D(D), .S0(S0), .S1(S1), .Y(Y),
//   .not_S0_out(not_S0_out), .not_S1_out(not_S1_out),
//   .and1_out(and1_out), .and2_out(and2_out), .and3_out(and3_out), .and4_out(and4_out)
// );