module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

// X must match the implemented AND/NOT/AND logic.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) & ~(B1 & B2))
    );

// A high X requires both A inputs to be high.
    check_x_requires_a_high: assert property (
        @(posedge clk) X |-> (A1 && A2)
    );

// A high X requires both B inputs to be low.
    check_x_requires_b_low: assert property (
        @(posedge clk) X |-> (!B1 && !B2)
    );

// Both A inputs high with both B inputs low must drive X high.
    check_a_high_b_low_sets_x: assert property (
        @(posedge clk) (A1 && A2 && !B1 && !B2) |-> X
    );

// Any low A input must force X low.
    check_a_low_clears_x: assert property (
        @(posedge clk) (!A1 || !A2) |-> !X
    );

// Any high B input must force X low.
    check_b_high_clears_x: assert property (
        @(posedge clk) (B1 || B2) |-> !X
    );

endmodule
