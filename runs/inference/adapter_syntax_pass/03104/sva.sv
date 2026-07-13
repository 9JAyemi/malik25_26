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

    // A high must drive X high.
    check_a_high_sets_x: assert property (
        @($global_clock) A |-> X
    );

    // B high must drive X high.
    check_b_high_sets_x: assert property (
        @($global_clock) B |-> X
    );

    // C high must drive X high.
    check_c_high_sets_x: assert property (
        @($global_clock) C |-> X
    );

    // All inputs low must drive X low.
    check_all_inputs_low_clear_x: assert property (
        @($global_clock) (!A && !B && !C) |-> !X
    );

    // X high must come from at least one high input.
    check_x_high_has_high_input: assert property (
        @($global_clock) X |-> (A || B || C)
    );

endmodule