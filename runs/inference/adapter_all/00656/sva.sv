module or3_4_custom_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must equal the OR of A, B, and C.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

    // If all inputs are low, X must be low.
    check_all_inputs_low: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // If any input is high, X must be high.
    check_any_input_high: assert property (
        @(posedge clk) (A || B || C) |-> X
    );

    // A high must force X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

    // B high must force X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

    // C high must force X high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> X
    );

    // X low means all inputs are low.
    check_x_low_means_all_inputs_low: assert property (
        @(posedge clk) !X |-> (!A && !B && !C)
    );

    // X high means at least one input is high.
    check_x_high_means_any_input_high: assert property (
        @(posedge clk) X |-> (A || B || C)
    );

endmodule