module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must equal the OR of the two AND terms.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

    // If the A-side AND term is true, X must be high.
    check_a_term_drives_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // If the B-side AND term is true, X must be high.
    check_b_term_drives_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If both AND terms are false, X must be low.
    check_no_terms_means_low: assert property (
        @(posedge clk) (!(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // If X is high, at least one AND term must be true.
    check_high_output_has_active_term: assert property (
        @(posedge clk) X |-> ((A1 & A2) || (B1 & B2))
    );

    // If X is low, both AND terms must be false.
    check_low_output_has_no_active_term: assert property (
        @(posedge clk) !X |-> (!(A1 & A2) && !(B1 & B2))
    );

    // With B-side inputs low, X reduces to the A-side AND term.
    check_b_side_low_reduces_to_a_term: assert property (
        @(posedge clk) (!B1 && !B2) |-> (X == (A1 & A2))
    );

    // With A-side inputs low, X reduces to the B-side AND term.
    check_a_side_low_reduces_to_b_term: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == (B1 & B2))
    );

    // With both A-side inputs high, X must be high.
    check_a_side_high_forces_high: assert property (
        @(posedge clk) (A1 && A2) |-> X
    );

    // With both B-side inputs high, X must be high.
    check_b_side_high_forces_high: assert property (
        @(posedge clk) (B1 && B2) |-> X
    );

endmodule