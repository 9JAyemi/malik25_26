module and_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must always equal the AND of A, B, and C.
    check_and_function: assert property (
        @($global_clock) Y === (A & B & C)
    );

    // Y high requires all three inputs high.
    check_y_high_requires_all_inputs_high: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b1) && (B === 1'b1) && (C === 1'b1))
    );

    // All three inputs high must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1)) |-> (Y === 1'b1)
    );

    // Any low input must drive Y low.
    check_any_low_input_drives_y_low: assert property (
        @($global_clock) ((A === 1'b0) || (B === 1'b0) || (C === 1'b0)) |-> (Y === 1'b0)
    );

endmodule