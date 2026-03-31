module sky130_fd_sc_lp__or2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // X must equal the OR of A and B.
    check_or_function: assert property (
        @(posedge clk) X == (A | B)
    );

    // If both inputs are low, X must be low.
    check_both_inputs_low: assert property (
        @(posedge clk) (!A && !B) |-> !X
    );

    // If A is high, X must be high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

    // If B is high, X must be high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

    // If X is low, both inputs must be low.
    check_x_low_requires_both_inputs_low: assert property (
        @(posedge clk) !X |-> (!A && !B)
    );

    // If X is high, at least one input must be high.
    check_x_high_requires_some_input_high: assert property (
        @(posedge clk) X |-> (A || B)
    );

endmodule