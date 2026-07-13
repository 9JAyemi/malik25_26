module OR3_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of A, B, and C.
    check_or_function: assert property (
        @($global_clock) X == (A | B | C)
    );

    // If all inputs are low, X must be low.
    check_all_inputs_low: assert property (
        @($global_clock) (!A && !B && !C) |-> !X
    );

    // If any input is high, X must be high.
    check_any_input_high: assert property (
        @($global_clock) (A || B || C) |-> X
    );

    // A high must force X high.
    check_a_high_sets_x: assert property (
        @($global_clock) A |-> X
    );

    // B high must force X high.
    check_b_high_sets_x: assert property (
        @($global_clock) B |-> X
    );

    // C high must force X high.
    check_c_high_sets_x: assert property (
        @($global_clock) C |-> X
    );

    // X low means all inputs are low.
    check_x_low_means_all_inputs_low: assert property (
        @($global_clock) !X |-> (!A && !B && !C)
    );

    // X high means at least one input is high.
    check_x_high_means_any_input_high: assert property (
        @($global_clock) X |-> (A || B || C)
    );

endmodule