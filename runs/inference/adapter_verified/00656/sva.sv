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

// A high must drive X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

// B high must drive X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

// C high must drive X high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> X
    );

// All inputs low must drive X low.
    check_all_low_clears_x: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

// X high implies at least one input is high.
    check_x_high_requires_some_input: assert property (
        @(posedge clk) X |-> (A || B || C)
    );

endmodule
