module nand4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // If A is low, the NAND output must be high.
    check_a_low_forces_y_high: assert property (
        @($global_clock) (A == 1'b0) |-> (Y == 1'b1)
    );

    // If B is low, the NAND output must be high.
    check_b_low_forces_y_high: assert property (
        @($global_clock) (B == 1'b0) |-> (Y == 1'b1)
    );

    // If C is low, the NAND output must be high.
    check_c_low_forces_y_high: assert property (
        @($global_clock) (C == 1'b0) |-> (Y == 1'b1)
    );

    // If D is low, the NAND output must be high.
    check_d_low_forces_y_high: assert property (
        @($global_clock) (D == 1'b0) |-> (Y == 1'b1)
    );

    // If all four inputs are high, the NAND output must be low.
    check_all_high_forces_y_low: assert property (
        @($global_clock)
        ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b0)
    );

    // A low output can only occur when all four inputs are high.
    check_y_low_implies_all_high: assert property (
        @($global_clock)
        (Y == 1'b0) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

endmodule