module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X matches the implemented sum-of-products function.
    check_x_function: assert property (
        @(posedge clk) X === ((A1 & A2 & A3) | (B1 & B2))
    );

    // The A-side 3-input AND drives X high.
    check_a_product_sets_x: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

    // The B-side 2-input AND drives X high.
    check_b_product_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // X is low when neither AND term is active.
    check_no_product_means_x_low: assert property (
        @(posedge clk) (!(A1 & A2 & A3) && !(B1 & B2)) |-> !X
    );

endmodule