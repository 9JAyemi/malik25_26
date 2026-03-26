module and_4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No explicit clock or reset; sample combinational behavior on $global_clock.

    // A low input forces Y low.
    check_a_low_forces_y_low: assert property (
        @($global_clock) (A === 1'b0) |-> (Y === 1'b0)
    );

    // B low input forces Y low.
    check_b_low_forces_y_low: assert property (
        @($global_clock) (B === 1'b0) |-> (Y === 1'b0)
    );

    // C low input forces Y low.
    check_c_low_forces_y_low: assert property (
        @($global_clock) (C === 1'b0) |-> (Y === 1'b0)
    );

    // D low input forces Y low.
    check_d_low_forces_y_low: assert property (
        @($global_clock) (D === 1'b0) |-> (Y === 1'b0)
    );

    // All four high inputs drive Y high.
    check_all_high_drives_y_high: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1)) |-> (Y === 1'b1)
    );

    // A high Y requires all four inputs high.
    check_y_high_requires_all_high: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b1) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1))
    );

    // With known inputs, Y matches the implemented 4-input AND.
    check_known_inputs_match_and_function: assert property (
        @($global_clock) (!$isunknown({A, B, C, D})) |-> (Y === ((A & B) & (C & D)))
    );

endmodule