module my_and2_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y must match the RTL AND of A and B.
    check_y_matches_and: assert property (
        @(posedge clk) Y == (A & B)
    );

    // A must be high whenever Y is high.
    check_y_high_requires_a_high: assert property (
        @(posedge clk) Y |-> A
    );

    // B must be high whenever Y is high.
    check_y_high_requires_b_high: assert property (
        @(posedge clk) Y |-> B
    );

    // Both inputs high must drive Y high.
    check_ab_high_implies_y_high: assert property (
        @(posedge clk) (A & B) |-> Y
    );

endmodule