module sky130_fd_sc_ls__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented AOI function.
    check_functional_equivalence: assert property (
        @(posedge clk)
        Y == (~((A1 & A2 & A3) | (B1 & B2)))
    );

    // All three A inputs high force Y low.
    check_a_term_forces_low: assert property (
        @(posedge clk)
        ((A1 & A2 & A3) == 1'b1) |-> (Y == 1'b0)
    );

    // Both B inputs high force Y low.
    check_b_term_forces_low: assert property (
        @(posedge clk)
        ((B1 & B2) == 1'b1) |-> (Y == 1'b0)
    );

    // Y is high when neither input product term is active.
    check_high_when_no_term_active: assert property (
        @(posedge clk)
        (((A1 & A2 & A3) == 1'b0) && ((B1 & B2) == 1'b0)) |-> (Y == 1'b1)
    );

    // A low Y must come from an active A or B term.
    check_low_has_valid_cause: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> (((A1 & A2 & A3) == 1'b1) || ((B1 & B2) == 1'b1))
    );

    // A high Y means both product terms are inactive.
    check_high_means_no_active_terms: assert property (
        @(posedge clk)
        (Y == 1'b1) |-> (((A1 & A2 & A3) == 1'b0) && ((B1 & B2) == 1'b0))
    );

endmodule