module sky130_fd_sc_ms__a221o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X must equal the OR of C1, A1&A2, and B1&B2.
    check_exact_or_function: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | C1)
    );

    // C1 alone is sufficient to drive X high.
    check_c1_forces_output_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together must drive X high.
    check_a_pair_forces_output_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high together must drive X high.
    check_b_pair_forces_output_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If all three OR terms are low, X must be low.
    check_output_low_when_all_terms_low: assert property (
        @(posedge clk) !(C1 | (A1 & A2) | (B1 & B2)) |-> !X
    );

    // If X is low, none of the OR terms can be high.
    check_output_low_implies_no_active_term: assert property (
        @(posedge clk) !X |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

    // If X is high, at least one of the OR terms must be high.
    check_output_high_implies_active_term: assert property (
        @(posedge clk) X |-> (C1 || (A1 & A2) || (B1 & B2))
    );

endmodule