module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

// Y matches the implemented NAND/AND/NOT function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((~A1 & ~A2) & (~B1 & ~B2))
    );

// A1 low and A2 low force Y high.
    check_y_high_when_a_pair_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> Y
    );

// B1 low and B2 low force Y high.
    check_y_high_when_b_pair_low: assert property (
        @(posedge clk) (!B1 && !B2) |-> Y
    );

// With both input pairs high, Y must be low.
    check_y_low_when_both_pairs_high: assert property (
        @(posedge clk) (A1 && A2 && B1 && B2) |-> !Y
    );

// A high Y requires at least one input pair to be low.
    check_y_high_implies_some_pair_low: assert property (
        @(posedge clk) Y |-> ((!A1 && !A2) || (!B1 && !B2))
    );

// A low Y requires both input pairs to be high.
    check_y_low_implies_both_pairs_high: assert property (
        @(posedge clk) !Y |-> (A1 && A2 && B1 && B2)
    );

endmodule
