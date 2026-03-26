module my_or_gate_assertions (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must always equal the OR of A, B, and C.
    check_or_function: assert property (
        @($global_clock) X === (A | B | C)
    );

    // A high must force X high.
    check_a_high_drives_x_high: assert property (
        @($global_clock) (A === 1'b1) |-> (X === 1'b1)
    );

    // B high must force X high.
    check_b_high_drives_x_high: assert property (
        @($global_clock) (B === 1'b1) |-> (X === 1'b1)
    );

    // C high must force X high.
    check_c_high_drives_x_high: assert property (
        @($global_clock) (C === 1'b1) |-> (X === 1'b1)
    );

    // X high must be caused by at least one high input.
    check_x_high_has_high_input: assert property (
        @($global_clock) (X === 1'b1) |-> ((A === 1'b1) || (B === 1'b1) || (C === 1'b1))
    );

    // All inputs low must force X low.
    check_all_inputs_low_drive_x_low: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (X === 1'b0)
    );

    // X low requires all inputs to be low.
    check_x_low_requires_all_inputs_low: assert property (
        @($global_clock) (X === 1'b0) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0))
    );

endmodule