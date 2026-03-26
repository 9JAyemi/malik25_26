module sky130_fd_sc_hs__a21bo_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND
);

    // X matches the implemented NAND-NAND-buffer function.
    check_output_matches_gate_chain: assert property (
        @($global_clock)
        X === ~(B1_N & ~(A1 & A2))
    );

    // When both A inputs are high, X must be high.
    check_a_inputs_high_drive_x_high: assert property (
        @($global_clock)
        (A1 && A2) |-> (X === 1'b1)
    );

    // When B1_N is low, X must be high.
    check_b1n_low_drives_x_high: assert property (
        @($global_clock)
        (!B1_N) |-> (X === 1'b1)
    );

    // With B1_N high and A1 low, X must be low.
    check_b1n_high_a1_low_drives_x_low: assert property (
        @($global_clock)
        (B1_N && !A1) |-> (X === 1'b0)
    );

    // With B1_N high and A2 low, X must be low.
    check_b1n_high_a2_low_drives_x_low: assert property (
        @($global_clock)
        (B1_N && !A2) |-> (X === 1'b0)
    );

    // X can be low only in the implemented low-output case.
    check_x_low_only_in_implemented_case: assert property (
        @($global_clock)
        (X === 1'b0) |-> (B1_N && !(A1 && A2))
    );

endmodule