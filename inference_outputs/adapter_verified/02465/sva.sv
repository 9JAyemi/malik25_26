module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

// X matches the RTL Boolean expression.
    check_functional_equivalence: assert property (
        @(posedge clk)
        X == (((A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1))) ? 1'b1 : 1'b0
    );

// A1 high and A2 low drives X high.
    check_a1_high_a2_low_sets_x: assert property (
        @(posedge clk)
        (A1 && !A2) |-> X
    );

// A2 high and A1 low with A3 high and B1 low drives X high.
    check_a2_high_a1_low_a3_high_b1_low_sets_x: assert property (
        @(posedge clk)
        (A2 && !A1 && A3 && !B1) |-> X
    );

// A1 and A2 both low with A3 high and B1 high drives X high.
    check_a1_a2_low_a3_high_b1_high_sets_x: assert property (
        @(posedge clk)
        (!A1 && !A2 && A3 && B1) |-> X
    );

// A1 and A2 both high drives X low.
    check_a1_a2_high_clears_x: assert property (
        @(posedge clk)
        (A1 && A2) |-> !X
    );

// A1 and A3 both high with B1 low drives X low.
    check_a1_a3_high_b1_low_clears_x: assert property (
        @(posedge clk)
        (A1 && A3 && !B1) |-> !X
    );

// A2 and A3 both high with B1 high drives X low.
    check_a2_a3_high_b1_high_clears_x: assert property (
        @(posedge clk)
        (A2 && A3 && B1) |-> !X
    );

// With A1 and A2 equal, X follows A3.
    check_equal_a1_a2_follows_a3: assert property (
        @(posedge clk)
        (A1 == A2) |-> (X == A3)
    );

// With A1 and A3 equal, X follows A2.
    check_equal_a1_a3_follows_a2: assert property (
        @(posedge clk)
        (A1 == A3) |-> (X == A2)
    );

// With A2 and A3 equal, X follows A1.
    check_equal_a2_a3_follows_a1: assert property (
        @(posedge clk)
        (A2 == A3) |-> (X == A1)
    );

endmodule
