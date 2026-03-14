module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    ///// Functional equivalence sampled on multiple input edges /////
    // Y equals NAND of ((A1|A2), D1, (B1 XNOR C1)) on A1 edge.
    check_Y_function_equivalence_on_A1: assert property (
        @(posedge A1) Y == ~((A1 | A2) & D1 & (B1 ~^ C1))
    );
    // Y equals NAND of ((A1|A2), D1, (B1 XNOR C1)) on A2 edge.
    check_Y_function_equivalence_on_A2: assert property (
        @(posedge A2) Y == ~((A1 | A2) & D1 & (B1 ~^ C1))
    );
    // Y equals NAND of ((A1|A2), D1, (B1 XNOR C1)) on B1 edge.
    check_Y_function_equivalence_on_B1: assert property (
        @(posedge B1) Y == ~((A1 | A2) & D1 & (B1 ~^ C1))
    );
    // Y equals NAND of ((A1|A2), D1, (B1 XNOR C1)) on C1 edge.
    check_Y_function_equivalence_on_C1: assert property (
        @(posedge C1) Y == ~((A1 | A2) & D1 & (B1 ~^ C1))
    );
    // Y equals NAND of ((A1|A2), D1, (B1 XNOR C1)) on D1 edge.
    check_Y_function_equivalence_on_D1: assert property (
        @(posedge D1) Y == ~((A1 | A2) & D1 & (B1 ~^ C1))
    );

    ///// Useful consequences of the logic /////
    // If all three NAND inputs are 1, Y must be 0.
    check_Y_low_when_all_true: assert property (
        @(posedge A1) (D1 && (A1 || A2) && (B1 == C1)) |-> (Y == 1'b0)
    );
    // If D1 is 0, Y must be 1 regardless of other inputs.
    check_Y_high_if_D1_low: assert property (
        @(posedge D1) (D1 == 1'b0) |-> (Y == 1'b1)
    );
    // If A1 and A2 are both 0 (A1|A2==0), Y must be 1.
    check_Y_high_if_A1A2_both_zero: assert property (
        @(posedge A2) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );
    // If B1 XOR C1 is 1 (XNOR input is 0), Y must be 1.
    check_Y_high_if_B1xorC1_one: assert property (
        @(posedge B1) ((B1 ^ C1) == 1'b1) |-> (Y == 1'b1)
    );
    // If Y is 0, then D1=1, (A1|A2)=1, and B1==C1 must all hold.
    check_zero_implies_all_inputs_true: assert property (
        @(posedge C1) (Y == 1'b0) |-> (D1 == 1'b1 && (A1 || A2) && (B1 == C1))
    );
endmodule