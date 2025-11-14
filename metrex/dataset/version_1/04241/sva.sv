// SVA checker for ripple_carry_adder
module rca_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout,
  input  logic [3:0] C // internal carries from DUT
);

  // Helper expressions
  let in_ok = !$isunknown({A,B,Cin});

  let c1e = (A[0] & B[0]) | (A[0] & Cin)  | (B[0] & Cin);
  let c2e = (A[1] & B[1]) | (A[1] & c1e)  | (B[1] & c1e);
  let c3e = (A[2] & B[2]) | (A[2] & c2e)  | (B[2] & c2e);

  let sum_e = { (A[3]^B[3]^c3e),
                (A[2]^B[2]^c2e),
                (A[1]^B[1]^c1e),
                (A[0]^B[0]^Cin) };

  // Golden functional correctness (5-bit add)
  assert property (@(*) in_ok |-> {Cout,Sum} == A + B + Cin)
    else $error("Adder result mismatch");

  // Internal ripple-carry chain is correct and wired as intended
  assert property (@(*) in_ok |-> (C[0] == Cin) && (C[1] == c1e) && (C[2] == c2e) && (C[3] == c3e))
    else $error("Carry chain mismatch");

  // Sum bits computed from expected carries
  assert property (@(*) in_ok |-> Sum == sum_e)
    else $error("Sum bits mismatch");

  // MSB carry-out equals internal C[3]
  assert property (@(*) in_ok |-> Cout == C[3])
    else $error("Cout wiring mismatch");

  // X-propagation check: clean outputs for clean inputs
  assert property (@(*) in_ok |-> !$isunknown({Sum,Cout,C}))
    else $error("X/Z detected on outputs with clean inputs");

  // Lightweight functional coverage
  cover property (@(*) in_ok && (Sum == 4'h0) && (Cout == 1'b0));               // zero result
  cover property (@(*) in_ok && (Cout == 1'b1));                                 // any overflow
  cover property (@(*) in_ok && &(A^B) && Cin && Cout);                          // full propagate chain ripples to MSB
  cover property (@(*) in_ok && |(A & B));                                       // any generate
  cover property (@(*) in_ok && (A == 4'hF) && (B == 4'hF) && (Cin == 1'b1));    // max + carry-in
  cover property (@(*) in_ok && (A == 4'hF) && (B == 4'h0) && (Cin == 1'b1));    // full ripple to overflow

endmodule

// Bind into DUT (accesses internal C)
bind ripple_carry_adder rca_sva u_rca_sva (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout), .C(C)
);