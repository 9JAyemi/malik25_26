// SVA for logic_module
// Bind this checker to the DUT
module logic_module_sva (
  input logic A1, A2, B1, B2,
  input logic Y
);
  // Golden reference (structurally identical to DUT)
  wire logic ref = (A1 & A2)
                 | ((A1 & ~B1 & ~B2) & ~(A2 | B1 | B2))
                 | (~A1 & ~A2 & B1 & B2);

  // Also a simplified form used when inputs are known (2-state compare)
  wire logic ref_simpl = (A1 & A2)
                       | (A1 & ~A2 & ~B1 & ~B2)
                       | (~A1 & ~A2 & B1 & B2);

  // Combinational, race-free checks
  always_comb begin
    // 4-state equivalence (allows X/Z propagation)
    assert (#0 (Y === ref))
      else $error("logic_module: 4-state mismatch Y=%0b ref=%0b A1=%0b A2=%0b B1=%0b B2=%0b",
                  Y, ref, A1, A2, B1, B2);

    // When inputs are known, Y must be known and equal to simplified function
    if (!$isunknown({A1,A2,B1,B2})) begin
      assert (#0 (Y == ref_simpl))
        else $error("logic_module: 2-state mismatch Y=%0b ref=%0b A1=%0b A2=%0b B1=%0b B2=%0b",
                    Y, ref_simpl, A1, A2, B1, B2);
      assert (#0 (!$isunknown(Y)))
        else $error("logic_module: Y is X/Z with known inputs A1=%0b A2=%0b B1=%0b B2=%0b",
                    A1, A2, B1, B2);
    end

    // Concise functional coverage
    cover (#0 (A1 & A2 & Y));                  // T1: A1&A2 drives Y=1
    cover (#0 (A1 & ~A2 & ~B1 & ~B2 & Y));     // T2: A1&~A2&~B1&~B2 drives Y=1
    cover (#0 (~A1 & ~A2 & B1 & B2 & Y));      // T3: ~A1&~A2&B1&B2 drives Y=1
    cover (#0 (!((A1 & A2) | (A1 & ~A2 & ~B1 & ~B2) | (~A1 & ~A2 & B1 & B2)) && !Y)); // a Y=0 case
  end
endmodule

bind logic_module logic_module_sva sva_logic_module (.*);