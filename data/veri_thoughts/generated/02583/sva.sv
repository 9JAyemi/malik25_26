module sky130_fd_sc_lp__nand3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);
    // Combinational NAND3; no clock/reset present. Sample on input/output edges.

    // Y implements 3-input NAND on posedge A.
    check_truth_on_posedge_A: assert property (
        @(posedge A) (Y == ~(A & B & C))
    );

    // Y implements 3-input NAND on negedge A.
    check_truth_on_negedge_A: assert property (
        @(negedge A) (Y == ~(A & B & C))
    );

    // Y implements 3-input NAND on posedge B.
    check_truth_on_posedge_B: assert property (
        @(posedge B) (Y == ~(A & B & C))
    );

    // Y implements 3-input NAND on negedge B.
    check_truth_on_negedge_B: assert property (
        @(negedge B) (Y == ~(A & B & C))
    );

    // Y implements 3-input NAND on posedge C.
    check_truth_on_posedge_C: assert property (
        @(posedge C) (Y == ~(A & B & C))
    );

    // Y implements 3-input NAND on negedge C.
    check_truth_on_negedge_C: assert property (
        @(negedge C) (Y == ~(A & B & C))
    );

    // When Y falls, all inputs must be HIGH.
    y_fall_requires_all_high: assert property (
        @(negedge Y) (A && B && C)
    );

    // When Y rises, at least one input must be LOW.
    y_rise_requires_any_low: assert property (
        @(posedge Y) (!A || !B || !C)
    );

    // Y can change only if at least one input changed.
    y_change_requires_input_change: assert property (
        @(posedge Y or negedge Y) (!$stable(A) || !$stable(B) || !$stable(C))
    );

    // If all inputs are HIGH, Y must be LOW at that sample.
    all_high_implies_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
            (A && B && C) |-> (Y == 1'b0)
    );
endmodule