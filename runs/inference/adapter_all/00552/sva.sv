module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic F
);

    // F must match the implemented case mapping.
    check_function_mapping: assert property (
        @(posedge clk)
        F == (A & ~B & ~C)
    );

    // A=000 selects m3.
    check_case_000: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b000) |-> (F == (A & ~B & ~C))
    );

    // A=001 selects m2.
    check_case_001: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b001) |-> (F == (A & ~B & ~C))
    );

    // A=010 selects m1.
    check_case_010: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b010) |-> (F == (A & ~B & ~C))
    );

    // A=011 selects m0.
    check_case_011: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b011) |-> (F == (A & ~B & ~C))
    );

    // A=100 selects m3.
    check_case_100: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b100) |-> (F == (A & ~B & ~C))
    );

    // A=101 selects m2.
    check_case_101: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b101) |-> (F == (A & ~B & ~C))
    );

    // A=110 selects m1.
    check_case_110: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b110) |-> (F == (A & ~B & ~C))
    );

    // A=111 selects m0.
    check_case_111: assert property (
        @(posedge clk)
        ({A, B, C} == 3'b111) |-> (F == (A & ~B & ~C))
    );

    // With A=0 and B=0, F reduces to ~C.
    check_ab00_reduction: assert property (
        @(posedge clk)
        (A == 1'b0 && B == 1'b0) |-> (F == ~C)
    );

    // With A=0 and B=1, F reduces to C.
    check_ab01_reduction: assert property (
        @(posedge clk)
        (A == 1'b0 && B == 1'b1) |-> (F == C)
    );

    // With A=1 and B=0, F reduces to ~C.
    check_ab10_reduction: assert property (
        @(posedge clk)
        (A == 1'b1 && B == 1'b0) |-> (F == ~C)
    );

    // With A=1 and B=1, F reduces to C.
    check_ab11_reduction: assert property (
        @(posedge clk)
        (A == 1'b1 && B == 1'b1) |-> (F == C)
    );

endmodule