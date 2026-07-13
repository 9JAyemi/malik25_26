module nor3_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must always equal the 3-input NOR of A, B, and C.
    check_nor_function: assert property (
        @($global_clock) Y == ~(A | B | C)
    );

    // If all inputs are LOW, Y must be HIGH.
    check_all_inputs_low_outputs_high: assert property (
        @($global_clock) (!A && !B && !C) |-> Y
    );

    // If any input is HIGH, Y must be LOW.
    check_any_input_high_outputs_low: assert property (
        @($global_clock) (A || B || C) |-> !Y
    );

    // A HIGH output implies all three inputs are LOW.
    check_output_high_requires_all_inputs_low: assert property (
        @($global_clock) Y |-> (!A && !B && !C)
    );

    // A LOW output implies at least one input is HIGH.
    check_output_low_requires_some_input_high: assert property (
        @($global_clock) !Y |-> (A || B || C)
    );

endmodule