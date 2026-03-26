module sky130_fd_sc_ms__nor3_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // Combinational NOR3 cell with no RTL clock or reset; sample on $global_clock.

    // Y must always equal the 3-input NOR of A, B, and C.
    check_output_matches_nor3_function: assert property (
        @($global_clock) (Y === ~(A | B | C))
    );

    // A asserted high forces Y low.
    check_a_high_forces_y_low: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B asserted high forces Y low.
    check_b_high_forces_y_low: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // C asserted high forces Y low.
    check_c_high_forces_y_low: assert property (
        @($global_clock) (C === 1'b1) |-> (Y === 1'b0)
    );

    // All inputs low produce a high output.
    check_all_inputs_low_produces_y_high: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (Y === 1'b1)
    );

    // A high output means all three inputs are low.
    check_y_high_requires_all_inputs_low: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0))
    );

endmodule