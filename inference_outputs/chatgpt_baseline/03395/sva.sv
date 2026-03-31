module AND3_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Z
);

    // Z must always equal the three-input AND of A, B, and C.
    check_and3_function: assert property (
        @($global_clock) Z == (A & B & C)
    );

    // If all three inputs are HIGH, Z must be HIGH.
    check_all_inputs_high_drives_z_high: assert property (
        @($global_clock) (A & B & C) |-> Z
    );

    // If Z is HIGH, all three inputs must be HIGH.
    check_z_high_requires_all_inputs_high: assert property (
        @($global_clock) Z |-> (A & B & C)
    );

    // If any input is LOW, Z must be LOW.
    check_any_low_input_drives_z_low: assert property (
        @($global_clock) ((!A) || (!B) || (!C)) |-> (!Z)
    );

endmodule