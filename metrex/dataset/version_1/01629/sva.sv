// SVA for adder4bit and full_adder
// Bind into the DUTs; uses clockless @(*) concurrent assertions

module adder4bit_sva (
  input  logic [3:0] A, B,
  input  logic       Ci,
  input  logic [3:0] S,
  input  logic       Co,
  // internal nets
  input  logic [3:0] c, x, y
);
  default clocking cb @(*); endclocking

  let sum5 = ({1'b0, A} + {1'b0, B} + Ci);

  // Top-level functional correctness
  assert property ( !$isunknown({A,B,Ci}) |-> (S  === sum5[3:0]) )
    else $error("S mismatch: expected %0h got %0h", sum5[3:0], S);

  assert property ( !$isunknown({A,B,Ci}) |-> (Co === ~sum5[4]) )
    else $error("Co mismatch: expected %0b got %0b", ~sum5[4], Co);

  // Internal y should be bitwise ~B except LSB equals B[0]
  assert property ( !$isunknown(B) |-> (y === {~B[3:1], B[0]}) )
    else $error("y mismatch wrt B");

  // Internal x must be per-bit full-adder sum using specified carries
  assert property ( !$isunknown({A,B,Ci}) |->
                    (x[0] === (A[0] ^ y[0] ^ Ci))      &&
                    (x[1] === (A[1] ^ y[1] ^ c[0]))    &&
                    (x[2] === (A[2] ^ y[2] ^ c[1]))    &&
                    (x[3] === (A[3] ^ y[3] ^ c[2])) )
    else $error("x bit-sum mismatch");

  // Outputs should never be X/Z when inputs are known
  assert property ( !$isunknown({A,B,Ci}) |-> !$isunknown({S,Co}) )
    else $error("S/Co unknown with known inputs");

  // Concise but meaningful coverage
  cover property ( sum5[4] == 0 );               // no carry-out
  cover property ( sum5[4] == 1 );               // carry-out
  cover property ( (A^B) == 4'hF && Ci == 0 );   // full propagate w/o Ci
  cover property ( (A^B) == 4'hF && Ci == 1 );   // full propagate with Ci
  cover property ( A == 4'h0 && B == 4'h0 && Ci == 0 ); // zero + zero
  cover property ( A == 4'hF && B == 4'hF && Ci == 1 ); // max + max + 1
endmodule

bind adder4bit adder4bit_sva adder4bit_sva_i (
  .A(A), .B(B), .Ci(Ci), .S(S), .Co(Co),
  .c(c), .x(x), .y(y)
);


// SVA for primitive full_adder (applies to all instances)
module full_adder_sva (
  input logic a, b, ci, s, co
);
  default clocking cb @(*); endclocking

  // Truth-function checks
  assert property ( !$isunknown({a,b,ci}) |-> (s  === (a ^ b ^ ci)) )
    else $error("FA s mismatch");

  assert property ( !$isunknown({a,b,ci}) |-> (co === ((a & b) | (ci & (a ^ b)))) )
    else $error("FA co mismatch");

  // Outputs known when inputs known
  assert property ( !$isunknown({a,b,ci}) |-> !$isunknown({s,co}) )
    else $error("FA s/co unknown with known inputs");

  // Coverage: propagate/generate/kill
  cover property ( (a ^ b) == 1'b1 && ci == 1'b0 ); // propagate 0
  cover property ( (a ^ b) == 1'b1 && ci == 1'b1 ); // propagate 1
  cover property ( (a & b) == 1'b1 );               // generate
  cover property ( (a == 1'b0) && (b == 1'b0) );    // kill
endmodule

bind full_adder full_adder_sva full_adder_sva_i (.a(a), .b(b), .ci(ci), .s(s), .co(co));