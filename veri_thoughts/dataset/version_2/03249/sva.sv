module nand_and_gate_sva (
    input logic A,
    input logic B,
    input logic Y
);

    // Y must equal the AND of the two inputs.
    check_output_matches_and: assert property (
        @($global_clock) Y == (A & B)
    );

    // Both low inputs must produce a low output.
    check_inputs_00_drive_low: assert property (
        @($global_clock) (!A && !B) |-> !Y
    );

    // A low and B high must produce a low output.
    check_inputs_01_drive_low: assert property (
        @($global_clock) (!A && B) |-> !Y
    );

    // A high and B low must produce a low output.
    check_inputs_10_drive_low: assert property (
        @($global_clock) (A && !B) |-> !Y
    );

    // Both high inputs must produce a high output.
    check_inputs_11_drive_high: assert property (
        @($global_clock) (A && B) |-> Y
    );

endmodule