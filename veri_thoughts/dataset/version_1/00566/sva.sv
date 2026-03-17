module OAI21X1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y matches the implemented NAND-of-OR function.
    check_function_equivalence: assert property (
        @($global_clock) Y == ~((A | B) & C)
    );

    // When C is low, Y must be high.
    check_c_low_forces_y_high: assert property (
        @($global_clock) !C |-> Y
    );

    // When C is high and both OR inputs are low, Y must be high.
    check_only_c_high_keeps_y_high: assert property (
        @($global_clock) (C && !A && !B) |-> Y
    );

    // When C and A are high, Y must be low.
    check_a_and_c_high_force_y_low: assert property (
        @($global_clock) (C && A) |-> !Y
    );

    // When C and B are high, Y must be low.
    check_b_and_c_high_force_y_low: assert property (
        @($global_clock) (C && B) |-> !Y
    );

    // A low Y implies C is high and at least one OR input is high.
    check_y_low_implies_active_input_path: assert property (
        @($global_clock) !Y |-> (C && (A || B))
    );

endmodule