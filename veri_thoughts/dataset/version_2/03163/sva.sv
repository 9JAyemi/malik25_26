module tkg_ao222_sva (
    input logic o,
    input logic i0,
    input logic i1,
    input logic i2,
    input logic i3,
    input logic i4,
    input logic i5
);

    // Output matches the implemented AO222 equation.
    check_output_equation: assert property (
        @($global_clock) o == ((i0 & i1 & i2) | (i3 & i4 & i5))
    );

    // The first 3-input product term drives the output high.
    check_first_product_term: assert property (
        @($global_clock) (i0 & i1 & i2) |-> o
    );

    // The second 3-input product term drives the output high.
    check_second_product_term: assert property (
        @($global_clock) (i3 & i4 & i5) |-> o
    );

    // If neither product term is true, the output must be low.
    check_no_product_term_means_low: assert property (
        @($global_clock) !((i0 & i1 & i2) | (i3 & i4 & i5)) |-> !o
    );

    // A high output must be caused by at least one product term.
    check_output_high_has_valid_cause: assert property (
        @($global_clock) o |-> ((i0 & i1 & i2) | (i3 & i4 & i5))
    );

endmodule