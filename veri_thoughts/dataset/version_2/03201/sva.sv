module nor_gate_sva (
    input logic A,
    input logic B,
    input logic Y
);

    // Output always equals the NOR of A and B.
    check_nor_function: assert property (
        @($global_clock) (Y === ~(A | B))
    );

    // Both low inputs produce a high output.
    check_both_inputs_low_drive_high: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // A high input forces the output low.
    check_a_high_drives_output_low: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high input forces the output low.
    check_b_high_drives_output_low: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // With A low, the output is the inversion of B.
    check_a_low_reduces_to_invert_b: assert property (
        @($global_clock) (A === 1'b0) |-> (Y === ~B)
    );

    // With B low, the output is the inversion of A.
    check_b_low_reduces_to_invert_a: assert property (
        @($global_clock) (B === 1'b0) |-> (Y === ~A)
    );

    // A high output requires both inputs to be low.
    check_output_high_requires_both_inputs_low: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

    // A low output requires at least one input to be high.
    check_output_low_requires_input_high: assert property (
        @($global_clock) (Y === 1'b0) |-> ((A === 1'b1) || (B === 1'b1))
    );

endmodule