module sky130_fd_sc_ls__nand3_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Combinational NAND3 cell; no clock/reset. Sample assertions on input posedges.

    // Y equals ~(A & B & C) when sampled on A rising edge.
    check_nand_truth_on_A: assert property (
        @(posedge A) Y == ~(A & B & C)
    );

    // Y equals ~(A & B & C) when sampled on B rising edge.
    check_nand_truth_on_B: assert property (
        @(posedge B) Y == ~(A & B & C)
    );

    // Y equals ~(A & B & C) when sampled on C rising edge.
    check_nand_truth_on_C: assert property (
        @(posedge C) Y == ~(A & B & C)
    );

    // If all inputs are HIGH then Y must be LOW (sampled on A).
    check_all_high_implies_low_on_A: assert property (
        @(posedge A) (A && B && C) |-> (Y == 1'b0)
    );

    // If all inputs are HIGH then Y must be LOW (sampled on B).
    check_all_high_implies_low_on_B: assert property (
        @(posedge B) (A && B && C) |-> (Y == 1'b0)
    );

    // If all inputs are HIGH then Y must be LOW (sampled on C).
    check_all_high_implies_low_on_C: assert property (
        @(posedge C) (A && B && C) |-> (Y == 1'b0)
    );

    // If any input is LOW then Y must be HIGH (sampled on A).
    check_any_low_implies_high_on_A: assert property (
        @(posedge A) ((!A) || (!B) || (!C)) |-> (Y == 1'b1)
    );

    // If any input is LOW then Y must be HIGH (sampled on B).
    check_any_low_implies_high_on_B: assert property (
        @(posedge B) ((!A) || (!B) || (!C)) |-> (Y == 1'b1)
    );

    // If any input is LOW then Y must be HIGH (sampled on C).
    check_any_low_implies_high_on_C: assert property (
        @(posedge C) ((!A) || (!B) || (!C)) |-> (Y == 1'b1)
    );
endmodule