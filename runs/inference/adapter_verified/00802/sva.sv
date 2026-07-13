module my_or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

// X matches the implemented OR/NOT function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

// A high forces X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

// B high forces X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

// C high forces X high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> X
    );

// D_N low forces X high.
    check_d_n_low_sets_x: assert property (
        @(posedge clk) !D_N |-> X
    );

// With all inputs inactive, X is low.
    check_all_inputs_inactive_clear_x: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> !X
    );

// A high X requires at least one active input.
    check_x_high_requires_active_input: assert property (
        @(posedge clk) X |-> (A || B || C || !D_N)
    );

endmodule
