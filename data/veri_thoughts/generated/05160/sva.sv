module sky130_fd_sc_hd__or4_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X equals the OR of A, B, C, and D.
    check_output_matches_or: assert property (
        @($global_clock) X === (A | B | C | D)
    );

    // All inputs low drives X low.
    check_all_inputs_low_drives_x_low: assert property (
        @($global_clock)
        ((A === 1'b0) && (B === 1'b0) && (C === 1'b0) && (D === 1'b0))
        |-> (X === 1'b0)
    );

    // A high drives X high.
    check_a_high_drives_x_high: assert property (
        @($global_clock) (A === 1'b1) |-> (X === 1'b1)
    );

    // B high drives X high.
    check_b_high_drives_x_high: assert property (
        @($global_clock) (B === 1'b1) |-> (X === 1'b1)
    );

    // C high drives X high.
    check_c_high_drives_x_high: assert property (
        @($global_clock) (C === 1'b1) |-> (X === 1'b1)
    );

    // D high drives X high.
    check_d_high_drives_x_high: assert property (
        @($global_clock) (D === 1'b1) |-> (X === 1'b1)
    );

    // X high requires at least one input high.
    check_x_high_has_asserted_input: assert property (
        @($global_clock)
        (X === 1'b1)
        |-> ((A === 1'b1) || (B === 1'b1) || (C === 1'b1) || (D === 1'b1))
    );

endmodule