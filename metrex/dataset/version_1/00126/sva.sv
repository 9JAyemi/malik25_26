// SVA for sky130_fd_sc_ls__o22ai: Y = ~((A1|A2) & (B1|B2)) = (~(A1|A2)) | (~(B1|B2))
module sky130_fd_sc_ls__o22ai_sva(input logic A1, A2, B1, B2, Y);
  logic a_or, b_or, y_ref;

  // Functional equivalence and 4-state correctness (structure-preserving)
  always_comb begin
    a_or  = (A1 | A2);
    b_or  = (B1 | B2);
    y_ref = (~a_or) | (~b_or);

    assert (Y === y_ref)
      else $error("o22ai func mismatch: Y=%b a_or=%b b_or=%b", Y, a_or, b_or);

    // Deterministic corner cases (including X-prop where resolvable)
    if (a_or === 1'b0)                         assert (Y === 1'b1) else $error("o22ai: a_or==0 => Y must be 1");
    if (b_or === 1'b0)                         assert (Y === 1'b1) else $error("o22ai: b_or==0 => Y must be 1");
    if ((a_or === 1'b1) && (b_or === 1'b1))    assert (Y === 1'b0) else $error("o22ai: a_or=b_or=1 => Y must be 0");

    // X-propagation determinism
    if ((a_or === 1'b1) && (b_or === 1'bx))    assert (Y === 1'bx) else $error("o22ai: a_or=1,b_or=X => Y must be X");
    if ((a_or === 1'bx) && (b_or === 1'b1))    assert (Y === 1'bx) else $error("o22ai: a_or=X,b_or=1 => Y must be X");
    if ((a_or === 1'bx) && (b_or === 1'bx))    assert (Y === 1'bx) else $error("o22ai: a_or=b_or=X => Y must be X");

    // When both terms known, Y must be known and equal to ~(a_or & b_or)
    if ((a_or !== 1'bx) && (b_or !== 1'bx))    assert ((Y !== 1'bx) && (Y === ~(a_or & b_or)))
                                               else $error("o22ai: both terms known => Y must be known and correct");
  end

  // Lightweight coverage
  default clocking cb @ (A1 or A2 or B1 or B2 or Y); endclocking

  // Cover all term-combinations
  cover property (a_or === 1'b0 && b_or === 1'b0);
  cover property (a_or === 1'b0 && b_or === 1'b1);
  cover property (a_or === 1'b1 && b_or === 1'b0);
  cover property (a_or === 1'b1 && b_or === 1'b1);

  // Output values and transitions
  cover property (Y === 1'b0);
  cover property (Y === 1'b1);
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Each input toggles
  cover property ($rose(A1)); cover property ($fell(A1));
  cover property ($rose(A2)); cover property ($fell(A2));
  cover property ($rose(B1)); cover property ($fell(B1));
  cover property ($rose(B2)); cover property ($fell(B2));
endmodule

bind sky130_fd_sc_ls__o22ai sky130_fd_sc_ls__o22ai_sva sva_i (.*);