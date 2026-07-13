module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must equal the AND of A1&A2 and the inverse of B1&B2.
    check_x_function: assert property (
        @(posedge clk) X == ((A1 & A2) & ~(B1 & B2))
    );

    // If both A inputs are high, X must be high.
    check_x_high_when_a_pair_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // If both B inputs are high, X must be low.
    check_x_low_when_b_pair_high: assert property (
        @(posedge clk) (B1 & B2) |-> !X
    );

    // If X is high, both A inputs must be high.
    check_x_implies_a_pair_high: assert property (
        @(posedge clk) X |-> (A1 & A2)
    );

    // If X is high, both B inputs must be low.
    check_x_implies_b_pair_low: assert property (
        @(posedge clk) X |-> !(B1 & B2)
    );

    // If X is low, at least one A input must be low.
    check_x_low_implies_a_pair_low: assert property (
        @(posedge clk) !X |-> !(A1 & A2)
    );

    // If X is low, at least one B input must be high.
    check_x_low_implies_b_pair_high: assert property (
        @(posedge clk) !X |-> (B1 | B2)
    );

endmodule