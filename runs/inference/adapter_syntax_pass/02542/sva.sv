module sky130_fd_sc_hs__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

    // Y must always implement the RTL NAND function.
    check_nand_function: assert property (
        @($global_clock) Y == ~(A_N & B)
    );

    // A low A_N input forces Y high.
    check_a_low_forces_y_high: assert property (
        @($global_clock) (A_N == 1'b0) |-> (Y == 1'b1)
    );

    // A low B input forces Y high.
    check_b_low_forces_y_high: assert property (
        @($global_clock) (B == 1'b0) |-> (Y == 1'b1)
    );

    // Both high inputs force Y low.
    check_both_inputs_high_force_y_low: assert property (
        @($global_clock) ((A_N == 1'b1) && (B == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y can only occur when both inputs are high.
    check_y_low_requires_both_inputs_high: assert property (
        @($global_clock) (Y == 1'b0) |-> ((A_N == 1'b1) && (B == 1'b1))
    );

endmodule