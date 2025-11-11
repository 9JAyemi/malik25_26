// SVA checker for my_or
module my_or_sva (
  input A, B, C, D,
  input X,
  input or0_out_X
);

  // Functional correctness: 4-input OR and non-inverting buffer
  assert property (@(A or B or C or D or or0_out_X or X)
                   X === (A | B | C | D))
    else $error("my_or: X != A|B|C|D");

  assert property (@(or0_out_X or X)
                   X === or0_out_X)
    else $error("my_or: buf mismatch (X != or0_out_X)");

  // No unknown on X when all inputs are known
  assert property (@(A or B or C or D or X)
                   (!$isunknown({A,B,C,D})) |-> !$isunknown(X))
    else $error("my_or: X is X/Z while inputs are all known");

  // Basic functional coverage
  cover property (@(A or B or C or D) X === 1'b0);
  cover property (@(A or B or C or D) X === 1'b1);
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Truth-table coverage of all input combinations (16 states)
  covergroup cg_inputs @(A or B or C or D);
    cp: coverpoint {A,B,C,D} { bins all_vals[] = {[0:15]}; }
  endgroup
  cg_inputs cg_inputs_inst = new();

endmodule

// Bind the checker to the DUT (accesses the internal or0_out_X)
bind my_or my_or_sva u_my_or_sva (
  .A(A), .B(B), .C(C), .D(D),
  .X(X),
  .or0_out_X(or0_out_X)
);