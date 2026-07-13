module sky130_fd_sc_ms__a211o_assertions (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must always match the implemented OR-of-products function.
    check_exact_or_of_products: assert property (
        @($global_clock) X == ((A1 & A2) | (B1 & C1))
    );

    // When the A-product is true, X must be high.
    check_a_product_sets_x: assert property (
        @($global_clock) (A1 & A2) |-> X
    );

    // When the B-product is true, X must be high.
    check_b_product_sets_x: assert property (
        @($global_clock) (B1 & C1) |-> X
    );

    // If neither product is true, X must be low.
    check_no_product_clears_x: assert property (
        @($global_clock) (!(A1 & A2) && !(B1 & C1)) |-> !X
    );

    // A high X must come from at least one true product term.
    check_x_high_has_valid_cause: assert property (
        @($global_clock) X |-> ((A1 & A2) || (B1 & C1))
    );

    // If A1 is low, the output reduces to the B-product term.
    check_a1_low_reduces_to_b_term: assert property (
        @($global_clock) !A1 |-> (X == (B1 & C1))
    );

    // If A2 is low, the output reduces to the B-product term.
    check_a2_low_reduces_to_b_term: assert property (
        @($global_clock) !A2 |-> (X == (B1 & C1))
    );

    // If B1 is low, the output reduces to the A-product term.
    check_b1_low_reduces_to_a_term: assert property (
        @($global_clock) !B1 |-> (X == (A1 & A2))
    );

    // If C1 is low, the output reduces to the A-product term.
    check_c1_low_reduces_to_a_term: assert property (
        @($global_clock) !C1 |-> (X == (A1 & A2))
    );

endmodule