// SVA for add_sub
module add_sub_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       sub,
  input  logic [3:0] sum,
  input  logic       overflow
);
  // Basic sanity (no X/Z on interface)
  assert property (@(A or B or sub or sum or overflow) !$isunknown({A,B,sub,sum,overflow}));

  // Golden functional relation (combinational, sampled after delta to avoid races)
  assert property (@(A or B or sub) 1'b1 |-> ##0
                   {overflow,sum} == (sub ? ({1'b0,A}-{1'b0,B}) : ({1'b0,A}+{1'b0,B})));

  // Explicit overflow semantics in each mode (redundant but intent-checking)
  assert property (@(A or B or sub) !sub |-> ##0 overflow == ((A + B) > 4'hF));
  assert property (@(A or B or sub)  sub |-> ##0 overflow == (A < B));

  // Coverage: modes and edge cases
  cover property (@(A or B or sub) !sub ##0 ((A + B) <= 4'hF));   // add, no carry
  cover property (@(A or B or sub) !sub ##0 ((A + B) >  4'hF));   // add, carry
  cover property (@(A or B or sub)  sub ##0 (A >= B));            // sub, no borrow
  cover property (@(A or B or sub)  sub ##0 (A <  B));            // sub, borrow
  cover property (@(A or B or sub) (A == B));                     // equality case
  cover property (@(A or B or sub) (A == 4'h0 && B == 4'h0));     // both zero
  cover property (@(A or B or sub) (A == 4'hF && B == 4'hF));     // both max
endmodule

// Bind to DUT
bind add_sub add_sub_sva u_add_sub_sva (.A(A), .B(B), .sub(sub), .sum(sum), .overflow(overflow));