module sky130_fd_sc_ms__a32o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // X matches the implemented sum-of-products function.
    check_x_full_function: assert property (
        @(posedge clk) X == ((A3 & A1 & A2) | (B1 & B2))
    );

    // The A-side 3-input product term drives X high.
    check_a_product_sets_x: assert property (
        @(posedge clk) (A3 & A1 & A2) |-> X
    );

    // The B-side 2-input product term drives X high.
    check_b_product_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If X is low, both implemented product terms must be low.
    check_x_low_needs_both_products_low: assert property (
        @(posedge clk) (!X) |-> (!(A3 & A1 & A2) && !(B1 & B2))
    );

    // With the B-side product term low, X follows the A-side product term.
    check_x_equals_a_product_when_b_product_low: assert property (
        @(posedge clk) !(B1 & B2) |-> (X == (A3 & A1 & A2))
    );

    // With the A-side product term low, X follows the B-side product term.
    check_x_equals_b_product_when_a_product_low: assert property (
        @(posedge clk) !(A3 & A1 & A2) |-> (X == (B1 & B2))
    );

endmodule