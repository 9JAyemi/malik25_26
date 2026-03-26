module my_module_assertions (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X implements the DUT's combinational equation.
    check_x_boolean_function: assert property (
        @($global_clock) X == ((A1 & A2) | C1 | B1)
    );

    // B1 drives X high through the OR gate.
    check_b1_sets_x: assert property (
        @($global_clock) B1 |-> X
    );

    // C1 drives X high through the OR gate.
    check_c1_sets_x: assert property (
        @($global_clock) C1 |-> X
    );

    // A1 and A2 high together drive X high through the AND path.
    check_a1_a2_and_sets_x: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // X is low when all OR inputs are low.
    check_x_low_when_all_terms_low: assert property (
        @($global_clock) !(B1 | C1 | (A1 & A2)) |-> !X
    );

    // X can only be high if one of its driving terms is high.
    check_x_high_has_valid_source: assert property (
        @($global_clock) X |-> (B1 | C1 | (A1 & A2))
    );

endmodule