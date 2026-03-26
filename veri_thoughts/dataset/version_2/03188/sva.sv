module math_op_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);

    // No RTL clock or reset; sample the combinational function on $global_clock.

    // Y must equal the implemented boolean function.
    check_y_matches_boolean_function: assert property (
        @($global_clock) Y == ((A & B) | C)
    );

    // C high must force Y high.
    check_c_high_forces_y_high: assert property (
        @($global_clock) C |-> Y
    );

    // A and B high together must force Y high.
    check_ab_high_forces_y_high: assert property (
        @($global_clock) (A & B) |-> Y
    );

    // With C low, A low must force Y low.
    check_a_low_and_c_low_force_y_low: assert property (
        @($global_clock) ((!C) & (!A)) |-> (!Y)
    );

    // With C low, B low must force Y low.
    check_b_low_and_c_low_force_y_low: assert property (
        @($global_clock) ((!C) & (!B)) |-> (!Y)
    );

    // If Y is high while C is low, both A and B must be high.
    check_y_high_without_c_requires_ab_high: assert property (
        @($global_clock) (Y & (!C)) |-> (A & B)
    );

    // If Y is low, neither C nor A&B can be asserting the output.
    check_y_low_requires_c_low_and_no_ab: assert property (
        @($global_clock) (!Y) |-> ((!C) & (!(A & B)))
    );

endmodule