module karnaugh_map_sva (
    input logic clk,
    input logic [3:0] x,
    input logic f
);

    // f must match the implemented sum-of-products equation.
    check_f_matches_sum_of_products: assert property (
        @(posedge clk)
        f == ((x[0] & x[1]) | (x[0] & x[2]) | (x[1] & x[3]) | (x[2] & x[3]))
    );

    // x[0] and x[1] high must drive f high.
    check_f_high_for_x0_x1: assert property (
        @(posedge clk)
        (x[0] & x[1]) |-> f
    );

    // x[0] and x[2] high must drive f high.
    check_f_high_for_x0_x2: assert property (
        @(posedge clk)
        (x[0] & x[2]) |-> f
    );

    // x[1] and x[3] high must drive f high.
    check_f_high_for_x1_x3: assert property (
        @(posedge clk)
        (x[1] & x[3]) |-> f
    );

    // x[2] and x[3] high must drive f high.
    check_f_high_for_x2_x3: assert property (
        @(posedge clk)
        (x[2] & x[3]) |-> f
    );

    // If all implemented product terms are low, f must be low.
    check_f_low_without_product_terms: assert property (
        @(posedge clk)
        !((x[0] & x[1]) | (x[0] & x[2]) | (x[1] & x[3]) | (x[2] & x[3])) |-> !f
    );

endmodule