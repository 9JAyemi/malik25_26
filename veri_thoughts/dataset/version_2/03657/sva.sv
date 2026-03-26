module xor_gate_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic VDD,
    input logic VSS
);

    // Y must equal A XOR B.
    check_y_matches_xor_function: assert property (
        @($global_clock) Y == (A ^ B)
    );

    // A high output implies the inputs differ.
    check_high_output_requires_different_inputs: assert property (
        @($global_clock) Y |-> (A ^ B)
    );

    // A low output implies the inputs are equal.
    check_low_output_requires_equal_inputs: assert property (
        @($global_clock) !Y |-> !(A ^ B)
    );

    // Both low inputs must drive Y low.
    check_00_inputs_drive_low: assert property (
        @($global_clock) (!A && !B) |-> !Y
    );

    // A low and B high must drive Y high.
    check_01_inputs_drive_high: assert property (
        @($global_clock) (!A && B) |-> Y
    );

    // A high and B low must drive Y high.
    check_10_inputs_drive_high: assert property (
        @($global_clock) (A && !B) |-> Y
    );

    // Both high inputs must drive Y low.
    check_11_inputs_drive_low: assert property (
        @($global_clock) (A && B) |-> !Y
    );

endmodule