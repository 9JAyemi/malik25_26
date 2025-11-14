// SVA checker for ripple_carry_adder
// Concise, high-quality assertions and coverage

module rca_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic [3:0] S,
  input logic       Cout,
  // bind to internals for structural ripple checks
  input logic [3:0] sum,
  input logic [3:0] carry_out  // only [2:0] used by DUT
);

  function automatic logic carry_next (logic a, logic b, logic cin);
    return (a & b) | (cin & (a ^ b));
  endfunction

  // Predicted ripple carries and sums
  logic [4:0] c;        // c[0]=Cin, c[4]=predicted Cout
  logic [3:0] s_pred;

  assign c[0]    = Cin;
  assign c[1]    = carry_next(A[0], B[0], c[0]);
  assign c[2]    = carry_next(A[1], B[1], c[1]);
  assign c[3]    = carry_next(A[2], B[2], c[2]);
  assign c[4]    = carry_next(A[3], B[3], c[3]);
  assign s_pred  = { A[3]^B[3]^c[3], A[2]^B[2]^c[2], A[1]^B[1]^c[1], A[0]^B[0]^c[0] };

  // Inputs-known -> outputs-known
  assert property (@(*) (!$isunknown({A,B,Cin})) |-> ##0 !$isunknown({S,Cout,sum,carry_out[2:0]}))
    else $error("rca: X/Z on outputs with known inputs");

  // Full arithmetic equivalence
  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 {Cout,S} == A + B + Cin)
    else $error("rca: {Cout,S} != A+B+Cin");

  // Bit-accurate sum and carry chain (structural ripple)
  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 S == s_pred)
    else $error("rca: S bits mismatch predicted ripple sum");

  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 sum == s_pred)
    else $error("rca: internal sum wire != predicted ripple sum");

  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 carry_out[0] == c[1])
    else $error("rca: carry_out[0] mismatch");
  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 carry_out[1] == c[2])
    else $error("rca: carry_out[1] mismatch");
  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 carry_out[2] == c[3])
    else $error("rca: carry_out[2] mismatch");
  assert property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 Cout == c[4])
    else $error("rca: Cout mismatch predicted final carry");

  // Output equals internal sum wiring
  assert property (@(*) ##0 S == sum)
    else $error("rca: S != sum wiring");

  // Functional coverage (key scenarios)
  // Any generate, propagate, kill seen across bits
  cover property (@(*) ##0 (|(A & B)));             // generate observed
  cover property (@(*) ##0 (|(A ^ B)));             // propagate observed
  cover property (@(*) ##0 (|(~A & ~B)));           // kill observed

  // No-carry and carry-out cases
  cover property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 (Cout == 0));
  cover property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 (Cout == 1));

  // Full carry-propagate chain (longest path)
  cover property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 ((A^B)==4'hF && (A&B)==4'h0 && Cin==1 && Cout==1));

  // Corner examples
  cover property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 (A==4'h0 && B==4'h0 && Cin==0 && S==4'h0 && Cout==0));
  cover property (@(*) disable iff ($isunknown({A,B,Cin})) ##0 (A==4'hF && B==4'hF && Cin==1 && Cout==1));

endmodule

// Bind the checker to the DUT (connect internal nets for structural checks)
bind ripple_carry_adder rca_sva u_rca_sva (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout),
  .sum(sum), .carry_out(carry_out)
);