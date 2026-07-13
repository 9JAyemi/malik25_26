module sky130_fd_sc_lp__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

// X equals (A1|A2|A3)&B1.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2 | A3) & B1)
    );

// B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// Any A high with B1 high forces X high.
    check_any_a_with_b1_high_forces_x_high: assert property (
        @(posedge clk) (B1 && (A1 || A2 || A3)) |-> X
    );

// X high implies B1 is high.
    check_x_high_implies_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

// X high implies at least one A is high.
    check_x_high_implies_any_a_high: assert property (
        @(posedge clk) X |-> (A1 || A2 || A3)
    );

// With B1 high, X equals (A1|A2|A3).
    check_b1_high_makes_x_equal_or: assert property (
        @(posedge clk) B1 |-> (X == (A1 | A2 | A3))
    );

// With B1 high, X low implies all A are low.
    check_b1_high_and_x_low_implies_all_a_low: assert property (
        @(posedge clk) (B1 && !X) |-> (!A1 && !A2 && !A3)
    );

endmodule
