module karnaugh_map_assert (
    input logic A,
    input logic B,
    input logic C,
    input logic F
);
    // F equals the RTL expression when sampled on A.
    check_function_equivalence_on_A: assert property (
        @(posedge A) F == ((~A & ~B) | (A & ~B) | (B & C))
    );
    // F equals the RTL expression when sampled on B.
    check_function_equivalence_on_B: assert property (
        @(posedge B) F == ((~A & ~B) | (A & ~B) | (B & C))
    );
    // F equals the RTL expression when sampled on C.
    check_function_equivalence_on_C: assert property (
        @(posedge C) F == ((~A & ~B) | (A & ~B) | (B & C))
    );
    // F equals the simplified form ~B | (B & C) on A edges.
    check_simplified_equivalence_on_A: assert property (
        @(posedge A) F == ((~B) | (B & C))
    );
    // If B is 0 then F must be 1 (A,C don't matter).
    check_B0_implies_F1_on_A: assert property (
        @(posedge A) (B != 1'b0) || (F == 1'b1)
    );
    // If B is 1 then F equals C.
    check_B1_implies_F_eq_C_on_A: assert property (
        @(posedge A) (B != 1'b1) || (F == C)
    );
    // If F is 0 then B must be 1 and C must be 0.
    check_F0_implies_B1C0_on_A: assert property (
        @(posedge A) (F != 1'b0) || ((B == 1'b1) && (C == 1'b0))
    );
    // If B and C are 1 then F must be 1.
    check_B1C1_implies_F1_on_A: assert property (
        @(posedge A) (!((B == 1'b1) && (C == 1'b1))) || (F == 1'b1)
    );
    // If B is 1 and C is 0 then F must be 0.
    check_B1C0_implies_F0_on_A: assert property (
        @(posedge A) (!((B == 1'b1) && (C == 1'b0))) || (F == 1'b0)
    );
    // If F is 1 then (~B) or (B & C) must hold.
    check_F1_implies_minterms_on_A: assert property (
        @(posedge A) (F != 1'b1) || ((~B) || (B && C))
    );
endmodule