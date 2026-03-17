module sky130_fd_sc_lp__or4_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the OR of all four inputs.
    check_or4_function: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // Any high input must drive X high.
    check_any_input_high_sets_x: assert property (
        @($global_clock) (A | B | C | D) |-> X
    );

    // All inputs low must drive X low.
    check_all_inputs_low_clear_x: assert property (
        @($global_clock) (!A && !B && !C && !D) |-> !X
    );

    // A high X must come from at least one high input.
    check_x_high_implies_input_high: assert property (
        @($global_clock) X |-> (A | B | C | D)
    );

    // A low X means all inputs are low.
    check_x_low_implies_all_inputs_low: assert property (
        @($global_clock) !X |-> (!A && !B && !C && !D)
    );

endmodule