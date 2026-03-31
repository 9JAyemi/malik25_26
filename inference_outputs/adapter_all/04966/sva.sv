module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must equal the OR of the two AND terms.
    check_x_matches_or_of_ands: assert property (
        @(posedge clk) X == ((A1 & A2 & A3) | (B1 & B2))
    );

    // A high X must come from at least one asserted AND term.
    check_x_high_has_active_term: assert property (
        @(posedge clk) X |-> ((A1 & A2 & A3) | (B1 & B2))
    );

    // If both AND terms are low, X must be low.
    check_x_low_when_both_terms_low: assert property (
        @(posedge clk) !(A1 & A2 & A3) && !(B1 & B2) |-> !X
    );

    // If A1, A2, and A3 are all high, X must be high.
    check_x_high_when_a_term_active: assert property (
        @(posedge clk) A1 & A2 & A3 |-> X
    );

    // If B1 and B2 are both high, X must be high.
    check_x_high_when_b_term_active: assert property (
        @(posedge clk) B1 & B2 |-> X
    );

    // If X is low, both AND terms must be low.
    check_x_low_implies_both_terms_low: assert property (
        @(posedge clk) !X |-> !(A1 & A2 & A3) && !(B1 & B2)
    );

endmodule