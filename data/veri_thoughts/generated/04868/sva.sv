module xor_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must implement the RTL equation.
    check_function_equivalence: assert property (
        @($global_clock) X == ((A ^ B) & C)
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @($global_clock) !C |-> !X
    );

    // C high makes X match A xor B.
    check_c_high_passes_xor: assert property (
        @($global_clock) C |-> (X == (A ^ B))
    );

    // Equal A and B force X low.
    check_equal_inputs_force_x_low: assert property (
        @($global_clock) !(A ^ B) |-> !X
    );

    // X high requires C high and A/B different.
    check_x_high_requires_c_and_xor: assert property (
        @($global_clock) X |-> (C && (A ^ B))
    );

    // C high with A/B different drives X high.
    check_c_and_xor_drive_x_high: assert property (
        @($global_clock) (C && (A ^ B)) |-> X
    );

endmodule