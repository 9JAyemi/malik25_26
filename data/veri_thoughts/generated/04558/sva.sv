module my_or_gate_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must always equal the OR of A, B, and C.
    check_or_equivalence: assert property (
        @($global_clock) X == (A | B | C)
    );

    // If all inputs are low, X must be low.
    check_all_inputs_low_gives_x_low: assert property (
        @($global_clock) !(A | B | C) |-> !X
    );

    // If A is high, X must be high.
    check_a_high_drives_x_high: assert property (
        @($global_clock) A |-> X
    );

    // If B is high, X must be high.
    check_b_high_drives_x_high: assert property (
        @($global_clock) B |-> X
    );

    // If C is high, X must be high.
    check_c_high_drives_x_high: assert property (
        @($global_clock) C |-> X
    );

    // If X is high, at least one input must be high.
    check_x_high_has_input_source: assert property (
        @($global_clock) X |-> (A | B | C)
    );

endmodule