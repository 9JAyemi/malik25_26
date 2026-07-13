module my_logic_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic Y
);
    // Y matches NAND of C1, B1, and (A1|A2).
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(C1 & B1 & (A1 | A2))
    );

    // If C1 is LOW, Y must be HIGH.
    check_Y_one_if_C1_low: assert property (
        @(posedge clk) (!C1) |-> (Y == 1'b1)
    );

    // If B1 is LOW, Y must be HIGH.
    check_Y_one_if_B1_low: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // If both A1 and A2 are LOW, Y must be HIGH.
    check_Y_one_if_both_A_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> (Y == 1'b1)
    );

    // If C1, B1, and (A1|A2) are HIGH, Y must be LOW.
    check_Y_zero_if_all_high: assert property (
        @(posedge clk) (C1 && B1 && (A1 || A2)) |-> (Y == 1'b0)
    );

    // If Y is LOW, then C1 and B1 are HIGH and (A1|A2) is HIGH.
    check_Y_zero_implies_all_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (C1 && B1 && (A1 || A2))
    );

    // If Y is HIGH, at least one input to the NAND is effectively LOW.
    check_Y_one_implies_not_all_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!C1 || !B1 || (!A1 && !A2))
    );

    // When C1 and B1 are HIGH, Y equals NOT(A1|A2).
    check_Y_when_C1_B1_high: assert property (
        @(posedge clk) (C1 && B1) |-> (Y == ~(A1 | A2))
    );

    // When C1 and (A1|A2) are HIGH, Y equals NOT(B1).
    check_Y_when_C1_and_orA_high: assert property (
        @(posedge clk) (C1 && (A1 || A2)) |-> (Y == ~B1)
    );

    // When B1 and (A1|A2) are HIGH, Y equals NOT(C1).
    check_Y_when_B1_and_orA_high: assert property (
        @(posedge clk) (B1 && (A1 || A2)) |-> (Y == ~C1)
    );
endmodule