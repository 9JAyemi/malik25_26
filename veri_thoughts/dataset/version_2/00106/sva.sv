module sky130_fd_sc_lp__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must implement the OR of the two AND terms.
    check_output_equation: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

    // If A1 and A2 are both high, X must be high.
    check_a_term_drives_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // If B1 and B2 are both high, X must be high.
    check_b_term_drives_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If neither AND term is active, X must be low.
    check_no_active_term_drives_low: assert property (
        @(posedge clk) !((A1 & A2) | (B1 & B2)) |-> !X
    );

    // If A1 and B1 are both low, both product terms are blocked and X must be low.
    check_a1_b1_low_forces_low: assert property (
        @(posedge clk) (!A1 && !B1) |-> !X
    );

    // If A2 and B2 are both low, both product terms are blocked and X must be low.
    check_a2_b2_low_forces_low: assert property (
        @(posedge clk) (!A2 && !B2) |-> !X
    );

endmodule