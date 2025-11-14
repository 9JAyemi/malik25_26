// SVA checker for ripple_carry_adder
// Binds to the DUT and verifies full functional correctness concisely.

`default_nettype none

module rca_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout
);

  // Propagate/Generate and canonical ripple carries/sums
  let p0 = A[0]^B[0]; let g0 = A[0]&B[0];
  let c0 = g0 | (Cin & p0);
  let s0 = p0 ^ Cin;

  let p1 = A[1]^B[1]; let g1 = A[1]&B[1];
  let c1 = g1 | (c0 & p1);
  let s1 = p1 ^ c0;

  let p2 = A[2]^B[2]; let g2 = A[2]&B[2];
  let c2 = g2 | (c1 & p2);
  let s2 = p2 ^ c1;

  let p3 = A[3]^B[3]; let g3 = A[3]&B[3];
  let c3 = g3 | (c2 & p3);   // true Cout
  let s3 = p3 ^ c2;

  // End-to-end functional correctness
  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    {Cout, S} == (A + B + Cin)
  else $error("Adder sum mismatch: A=%0h B=%0h Cin=%0b -> got {Cout,S}=%0h expected=%0h",
              A,B,Cin,{Cout,S},(A+B+Cin));

  // Bit-level ripple-carry structure
  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    (S == {s3,s2,s1,s0}) && (Cout == c3)
  else $error("Bit-level ripple mismatch");

  // Clean-inputs must yield clean-outputs
  assert property (@(*))
    (!$isunknown({A,B,Cin})) |-> (!$isunknown({S,Cout}))
  else $error("X/Z on outputs with clean inputs");

  // Corner identities
  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    (B==4'b0 && Cin==1'b0) |-> (S==A && Cout==1'b0);

  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    (A==4'b0 && Cin==1'b0) |-> (S==B && Cout==1'b0);

  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    ((A==~B) && Cin==1'b0) |-> (S==4'hF && Cout==1'b0);

  assert property (@(*) disable iff ($isunknown({A,B,Cin})))
    ((A==~B) && Cin==1'b1) |-> (S==4'h0 && Cout==1'b1);

  // Minimal but meaningful coverage
  cover property (@(*) {Cout,S} == 5'h00); // zero + no carry
  cover property (@(*) {Cout,S} == 5'h0F); // sum max w/o carry
  cover property (@(*) {Cout,S} == 5'h10); // wrap to 0 with carry
  cover property (@(*) c0);
  cover property (@(*) c1);
  cover property (@(*) c2);
  cover property (@(*) c3);
  cover property (@(*) (!g3 && p3 && c2 && Cout)); // carry via propagate chain
  cover property (@(*) ( g3 && Cout));             // carry via MSB generate

endmodule

bind ripple_carry_adder rca_sva rca_chk (
  .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout)
);