module six_input_one_output_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    input logic Y
);

    // Y must match the implemented OR-of-ANDs function.
    check_y_matches_function: assert property (
        @($global_clock) (Y == ((A1 & A2) | (B1 & B2) | (C1 & C2)))
    );

    // The A input pair being high must make Y high.
    check_a_pair_implies_y: assert property (
        @($global_clock) ((A1 & A2) |-> Y)
    );

    // The B input pair being high must make Y high.
    check_b_pair_implies_y: assert property (
        @($global_clock) ((B1 & B2) |-> Y)
    );

    // The C input pair being high must make Y high.
    check_c_pair_implies_y: assert property (
        @($global_clock) ((C1 & C2) |-> Y)
    );

    // A high Y must be caused by at least one asserted input pair.
    check_y_has_active_pair: assert property (
        @($global_clock) (Y |-> ((A1 & A2) | (B1 & B2) | (C1 & C2)))
    );

    // If no input pair is fully asserted, Y must be low.
    check_no_pair_means_y_low: assert property (
        @($global_clock) (!((A1 & A2) | (B1 & B2) | (C1 & C2)) |-> !Y)
    );

endmodule