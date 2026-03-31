module sky130_fd_sc_ls__or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

// X equals A|B|C|~D_N.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

// When all inputs are 0, X must be 0.
    check_all_zero_implies_zero: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> (X == 1'b0)
    );

// When any input is 1, X must be 1.
    check_any_one_implies_one: assert property (
        @(posedge clk) (A || B || C || !D_N) |-> (X == 1'b1)
    );

// A high forces X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

// B high forces X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> (X == 1'b1)
    );

// C high forces X high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> (X == 1'b1)
    );

// D_N low forces X high.
    check_dn_low_sets_x: assert property (
        @(posedge clk) !D_N |-> (X == 1'b1)
    );

// X low implies all inputs are 0.
    check_zero_implies_all_zero: assert property (
        @(posedge clk) (X == 1'b0) |-> (!A && !B && !C && D_N)
    );

// X high implies at least one input is 1.
    check_one_implies_any_one: assert property (
        @(posedge clk) (X == 1'b1) |-> (A || B || C || !D_N)
    );

endmodule
