module and_comb_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must equal the AND of the two pairwise AND terms.
    check_x_matches_structural_and: assert property (
        @(posedge clk) X == ((A1 & A2) & (B1 & B2))
    );

    // Both input pairs high must drive X high.
    check_both_pairs_high_drive_x_high: assert property (
        @(posedge clk) ((A1 & A2) & (B1 & B2)) |-> X
    );

    // A low A-pair must force X low.
    check_a_pair_low_forces_x_low: assert property (
        @(posedge clk) !(A1 & A2) |-> !X
    );

    // A low B-pair must force X low.
    check_b_pair_low_forces_x_low: assert property (
        @(posedge clk) !(B1 & B2) |-> !X
    );

    // A high X requires both pairwise AND terms to be high.
    check_x_high_requires_both_pairs_high: assert property (
        @(posedge clk) X |-> ((A1 & A2) & (B1 & B2))
    );

endmodule