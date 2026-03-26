module a221o_2_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y
);

    // Y must match the implemented sum-of-products equation.
    check_output_equation: assert property (
        @(posedge clk)
        Y == ((A1 & B1 & C1) | (A2 & B2 & C1))
    );

    // C1 low forces Y low.
    check_c1_low_forces_y_low: assert property (
        @(posedge clk)
        !C1 |-> !Y
    );

    // The A1/B1 path is sufficient to drive Y high.
    check_first_product_term_drives_y: assert property (
        @(posedge clk)
        (A1 & B1 & C1) |-> Y
    );

    // The A2/B2 path is sufficient to drive Y high.
    check_second_product_term_drives_y: assert property (
        @(posedge clk)
        (A2 & B2 & C1) |-> Y
    );

    // Y high requires C1 to be high.
    check_y_implies_c1_high: assert property (
        @(posedge clk)
        Y |-> C1
    );

    // Y high requires at least one input pair product to be true.
    check_y_implies_product_term: assert property (
        @(posedge clk)
        Y |-> ((A1 & B1) | (A2 & B2))
    );

    // X is unused; changing only X cannot change Y.
    check_x_has_no_effect_on_y: assert property (
        @(posedge clk)
        ($changed(X) && $stable({A1, A2, B1, B2, C1})) |-> $stable(Y)
    );

endmodule