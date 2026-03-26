module four_to_one_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented OR-of-ANDs function.
    check_y_function: assert property (
        @($global_clock) (Y === ((A1 & A2) | (B1 & B2)))
    );

    // A1 and A2 both high force Y high.
    check_a_pair_sets_y: assert property (
        @($global_clock) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === 1'b1)
    );

    // B1 and B2 both high force Y high.
    check_b_pair_sets_y: assert property (
        @($global_clock) ((B1 === 1'b1) && (B2 === 1'b1)) |-> (Y === 1'b1)
    );

    // A high Y must come from at least one asserted input pair.
    check_y_high_has_valid_source: assert property (
        @($global_clock) (Y === 1'b1) |-> ((((A1 & A2) | (B1 & B2)) === 1'b1))
    );

    // A low Y means both product terms are broken.
    check_y_low_requires_broken_pairs: assert property (
        @($global_clock) (Y === 1'b0) |-> (((A1 === 1'b0) || (A2 === 1'b0)) && ((B1 === 1'b0) || (B2 === 1'b0)))
    );

    // A1 low and B1 low force Y low.
    check_a1_b1_low_force_y_low: assert property (
        @($global_clock) ((A1 === 1'b0) && (B1 === 1'b0)) |-> (Y === 1'b0)
    );

    // A1 low and B2 low force Y low.
    check_a1_b2_low_force_y_low: assert property (
        @($global_clock) ((A1 === 1'b0) && (B2 === 1'b0)) |-> (Y === 1'b0)
    );

    // A2 low and B1 low force Y low.
    check_a2_b1_low_force_y_low: assert property (
        @($global_clock) ((A2 === 1'b0) && (B1 === 1'b0)) |-> (Y === 1'b0)
    );

    // A2 low and B2 low force Y low.
    check_a2_b2_low_force_y_low: assert property (
        @($global_clock) ((A2 === 1'b0) && (B2 === 1'b0)) |-> (Y === 1'b0)
    );

endmodule