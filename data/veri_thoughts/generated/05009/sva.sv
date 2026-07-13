module karnaugh_map_assertions (
    input logic clk,
    input logic x1,
    input logic x2,
    input logic x3,
    input logic x4,
    input logic y
);

    // y must match the RTL sum-of-products equation.
    check_y_matches_sum_of_products: assert property (
        @(posedge clk)
        y == ((x1 & x4) |
              (x1 & x2 & x3) |
              (x1 & x2 & x4) |
              (x1 & x3 & x4) |
              (x2 & x3 & x4) |
              (x2 & x4) |
              (x3 & x4) |
              (x1 & x2 & x3 & x4))
    );

    // With x4 low, only the x1x2x3 term can make y high.
    check_x4_low_only_x123_controls_y: assert property (
        @(posedge clk)
        (!x4) |-> (y == (x1 & x2 & x3))
    );

    // With x4 high, y reduces to x1 OR x2 OR x3.
    check_x4_high_reduces_to_or123: assert property (
        @(posedge clk)
        x4 |-> (y == (x1 | x2 | x3))
    );

    // If x1, x2, and x3 are all low, y must be low.
    check_all_x123_low_forces_y_low: assert property (
        @(posedge clk)
        (!(x1 | x2 | x3)) |-> (!y)
    );

    // If x1, x2, and x3 are all high, y must be high.
    check_x123_high_forces_y_high: assert property (
        @(posedge clk)
        (x1 & x2 & x3) |-> y
    );

    // Any asserted x1, x2, or x3 with x4 high must drive y high.
    check_x4_with_any_x123_sets_y: assert property (
        @(posedge clk)
        (x4 & (x1 | x2 | x3)) |-> y
    );

    // If y is high while x4 is low, x1, x2, and x3 must all be high.
    check_y_high_without_x4_requires_x123: assert property (
        @(posedge clk)
        (y & !x4) |-> (x1 & x2 & x3)
    );

    // If y is high while x4 is high, at least one of x1, x2, or x3 must be high.
    check_y_high_with_x4_requires_any_x123: assert property (
        @(posedge clk)
        (y & x4) |-> (x1 | x2 | x3)
    );

endmodule