// SVA for comparator. Bind this to the DUT.
// Concise, checks functional equivalence, internal wires, X-prop, and adds focused coverage.

module comparator_sva
(
  input  logic [3:0] A, B, C, D,
  input  logic       EQ, GT,
  input  logic       a_greater_b, c_greater_d
);

  // Functional correctness of internal wires
  assert property (@(A or B or C or D) ##0 (a_greater_b == (A > B)));
  assert property (@(A or B or C or D) ##0 (c_greater_d == (C > D)));

  // EQ function
  assert property (@(A or B or C or D) ##0 (EQ == ((A == B) && (B == C) && (C == D))));

  // GT function (both via internals and directly)
  assert property (@(A or B or C or D) ##0 (GT == (a_greater_b || ((A == B) && c_greater_d))));
  assert property (@(A or B or C or D) ##0 (GT == ((A > B) || ((A == B) && (C > D)))));

  // Consistency between outputs
  assert property (@(A or B or C or D) ##0 (EQ |-> !GT));

  // No spurious output toggles without input changes
  assert property (@(A or B or C or D or EQ or GT)
                   ($changed({EQ,GT})) |-> $changed({A,B,C,D}));

  // No X/Z on outputs/internals when inputs are known
  assert property (@(A or B or C or D or EQ or GT)
                   (!$isunknown({A,B,C,D})) |-> ##0 !$isunknown({EQ,GT,a_greater_b,c_greater_d}));

  // Coverage: key behavior modes
  cover property (@(A or B or C or D) ##0 (A == B && B == C && C == D && EQ && !GT));                 // all equal
  cover property (@(A or B or C or D) ##0 (A > B && GT && !EQ));                                      // GT via A>B
  cover property (@(A or B or C or D) ##0 (A == B && C > D && GT && !EQ));                            // GT via tie-break
  cover property (@(A or B or C or D) ##0 (A < B && !GT && !EQ));                                     // A<B, GT=0
  cover property (@(A or B or C or D) ##0 (A == B && C <= D && !GT));                                 // tie, no GT

endmodule

// Bind into all comparator instances; connects to internals by name.
bind comparator comparator_sva comparator_sva_i (.*);