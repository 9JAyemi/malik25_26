module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must equal the OR of the two 3-input AND terms.
    check_x_matches_or_of_ands: assert property (
        @(posedge clk) X == ((A1 & A2 & A3) | (B1 & B2))
    );

    // A1, A2, and A3 high must drive X high.
    check_a_triplet_drives_x_high: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

    // B1 and B2 high must drive X high.
    check_b_pair_drives_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If neither AND term is true, X must be low.
    check_no_active_term_means_x_low: assert property (
        @(posedge clk) (!(A1 & A2 & A3) && !(B1 & B2)) |-> !X
    );

    // X high must come from at least one active AND term.
    check_x_high_has_valid_source: assert property (
        @(posedge clk) X |-> ((A1 & A2 & A3) || (B1 & B2))
    );

endmodule