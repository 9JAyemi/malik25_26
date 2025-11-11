// Bind these SVA into the DUT
bind my_module my_module_sva_checker();

module my_module_sva_checker;
  // Combinational functional/spec checks
  always_comb begin
    // Gate-level correctness
    assert (and1_out === (A1 & A2)) else $error("and1_out != A1&A2");
    assert (and2_out === (B1 & B2)) else $error("and2_out != B1&B2");
    assert (not1_out === ~and2_out) else $error("not1_out != ~and2_out");
    assert (X === (and1_out & not1_out)) else $error("X != and1_out & not1_out");

    // Spec equivalence
    assert (X === ((A1 & A2) & ~(B1 & B2))) else $error("X != (A1&A2)&~(B1&B2)");

    // Useful implications for quick debug
    assert (!X || (A1 & A2)) else $error("X implies A1&A2 violated");
    assert (!X || ~(B1 & B2)) else $error("X implies ~(B1&B2) violated");
  end

  // Coverage: toggle each internal/output and hit all functional quadrants
  cover property (@(posedge and1_out) 1);
  cover property (@(negedge and1_out) 1);
  cover property (@(posedge and2_out) 1);
  cover property (@(negedge and2_out) 1);
  cover property (@(posedge not1_out) 1);
  cover property (@(negedge not1_out) 1);
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  cover property ((A1 & A2) && (B1 & B2));   // expect X==0
  cover property ((A1 & A2) && ~(B1 & B2));  // expect X==1
  cover property (~(A1 & A2) && (B1 & B2));  // expect X==0
  cover property (~(A1 & A2) && ~(B1 & B2)); // expect X==0
endmodule