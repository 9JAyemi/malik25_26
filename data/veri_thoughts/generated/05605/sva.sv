module bitwise_xor_sva (
    input logic A,
    input logic B,
    input logic X
);

    // No RTL clock or reset; sample combinational behavior on the global assertion clock.

    // X must always equal A XOR B.
    check_xor_function: assert property (
        @($global_clock) X == (A ^ B)
    );

    // Matching inputs must drive X low.
    check_equal_inputs_drive_low: assert property (
        @($global_clock) (A == B) |-> (X == 1'b0)
    );

    // Different inputs must drive X high.
    check_different_inputs_drive_high: assert property (
        @($global_clock) (A != B) |-> (X == 1'b1)
    );

endmodule