// SVA for sky130_fd_sc_lp__o32a: X = (A1|A2|A3) & (B1|B2)
// Bind into each DUT instance so we can see internal nets.
module o32a_sva;
  default clocking cb @(*); endclocking

  // Local refs (4-state)
  wire left_or  = (A1 | A2 | A3);
  wire right_or = (B1 | B2);

  // Functional equivalence (strong 4-state)
  assert property (X === (left_or & right_or));

  // Internal stage equivalence
  assert property (or0_out     === left_or);
  assert property (or1_out     === right_or);
  assert property (and0_out_X  === (or0_out & or1_out));
  assert property (X           === and0_out_X);

  // Deterministic outcomes with partial knowledge
  assert property ((B1===1'b0 && B2===1'b0) |-> (X===1'b0));               // right_or=0 => X=0
  assert property ((A1===1'b0 && A2===1'b0 && A3===1'b0) |-> (X===1'b0));  // left_or=0 => X=0
  assert property (((A1===1'b1 || A2===1'b1 || A3===1'b1) &&
                    (B1===1'b1 || B2===1'b1)) |-> (X===1'b1));             // both ORs asserted => X=1

  // If all inputs are known, output must be known and 2-state correct
  assert property (!($isunknown({A1,A2,A3,B1,B2})) |-> (X == ((A1|A2|A3) & (B1|B2))));

  // No spurious output change without an input change
  assert property ($changed(X) |-> $changed({A1,A2,A3,B1,B2}));

  // Coverage: all truth-table quadrants and output toggles
  cover property (left_or==1'b1 && right_or==1'b1 && X==1'b1);
  cover property (left_or==1'b0 && right_or==1'b1 && X==1'b0);
  cover property (left_or==1'b1 && right_or==1'b0 && X==1'b0);
  cover property (left_or==1'b0 && right_or==1'b0 && X==1'b0);
  cover property ($rose(X));
  cover property ($fell(X));
endmodule

bind sky130_fd_sc_lp__o32a o32a_sva o32a_sva_i();