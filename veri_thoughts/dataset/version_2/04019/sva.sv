module sky130_fd_sc_hvl__or2_sva (
    input logic X,
    input logic A,
    input logic B
);

    // No RTL clock or reset; sample this combinational cell on the formal global clock.

    // X must always equal the OR of A and B.
    check_or_truth_function: assert property (
        @($global_clock) X == (A | B)
    );

    // If either input is high, the output must be high.
    check_or_any_input_high_sets_x: assert property (
        @($global_clock) (A || B) |-> X
    );

    // If both inputs are low, the output must be low.
    check_or_both_inputs_low_clears_x: assert property (
        @($global_clock) (!A && !B) |-> !X
    );

endmodule