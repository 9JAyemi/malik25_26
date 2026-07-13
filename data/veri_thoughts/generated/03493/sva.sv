module sky130_fd_sc_hs__o311ai_2_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y must equal the implemented OR-of-ANDs function.
    check_y_matches_boolean_function: assert property (
        @(posedge clk) (Y == ((A1 & A2 & A3) | (B1 & C1)))
    );

    // The A1/A2/A3 product term forces Y high.
    check_a_triplet_term_drives_y_high: assert property (
        @(posedge clk) (((A1 & A2 & A3) == 1'b1) |-> (Y == 1'b1))
    );

    // The B1/C1 product term forces Y high.
    check_bc_pair_term_drives_y_high: assert property (
        @(posedge clk) (((B1 & C1) == 1'b1) |-> (Y == 1'b1))
    );

    // If neither product term is true, Y must be low.
    check_no_active_term_drives_y_low: assert property (
        @(posedge clk) ((((A1 & A2 & A3) == 1'b0) && ((B1 & C1) == 1'b0)) |-> (Y == 1'b0))
    );

    // A high Y must come from at least one implemented product term.
    check_y_high_has_valid_cause: assert property (
        @(posedge clk) ((Y == 1'b1) |-> (((A1 & A2 & A3) == 1'b1) || ((B1 & C1) == 1'b1)))
    );

    // A low Y means both implemented product terms are low.
    check_y_low_means_no_active_term: assert property (
        @(posedge clk) ((Y == 1'b0) |-> (((A1 & A2 & A3) == 1'b0) && ((B1 & C1) == 1'b0)))
    );

endmodule