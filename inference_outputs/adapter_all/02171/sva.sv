module sky130_fd_sc_ls__a222o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

    // X must match the OR of the three 2-input AND terms.
    check_x_matches_or_of_ands: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // A high X must come from at least one asserted AND term.
    check_x_high_has_active_term: assert property (
        @(posedge clk) X |-> ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // If all AND terms are low, X must be low.
    check_no_active_term_means_x_low: assert property (
        @(posedge clk) !(A1 & A2 & B1 & B2 & C1 & C2) |-> !X
    );

    // If A1 and A2 are high, X must be high.
    check_a_term_drives_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // If B1 and B2 are high, X must be high.
    check_b_term_drives_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If C1 and C2 are high, X must be high.
    check_c_term_drives_x_high: assert property (
        @(posedge clk) (C1 & C2) |-> X
    );

    // If X is low, all AND terms must be low.
    check_x_low_means_no_active_term: assert property (
        @(posedge clk) !X |-> !(A1 & A2 & B1 & B2 & C1 & C2)
    );

    // If A1 and A2 are low, X must be low.
    check_a_term_low_forces_x_low: assert property (
        @(posedge clk) !(A1 & A2) |-> !X
    );

    // If B1 and B2 are low, X must be low.
    check_b_term_low_forces_x_low: assert property (
        @(posedge clk) !(B1 & B2) |-> !X
    );

    // If C1 and C2 are low, X must be low.
    check_c_term_low_forces_x_low: assert property (
        @(posedge clk) !(C1 & C2) |-> !X
    );

endmodule