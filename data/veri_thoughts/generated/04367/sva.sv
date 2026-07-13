module ao22_assertions (
    input logic clk,
    input logic q,
    input logic i0,
    input logic i1,
    input logic i2,
    input logic i3
);

    // q matches the AO22 combinational equation.
    check_q_matches_ao22_equation: assert property (
        @(posedge clk) q == ((i0 & i1) | (i2 & i3))
    );

    // The first AND term forces q high.
    check_first_and_term_forces_q_high: assert property (
        @(posedge clk) (i0 & i1) |-> q
    );

    // The second AND term forces q high.
    check_second_and_term_forces_q_high: assert property (
        @(posedge clk) (i2 & i3) |-> q
    );

    // q is low when both AND terms are low.
    check_no_and_terms_means_q_low: assert property (
        @(posedge clk) (!(i0 & i1) && !(i2 & i3)) |-> !q
    );

    // If q is high without the first term, the second term must be high.
    check_q_high_without_first_term_needs_second: assert property (
        @(posedge clk) (q && !(i0 & i1)) |-> (i2 & i3)
    );

    // If q is high without the second term, the first term must be high.
    check_q_high_without_second_term_needs_first: assert property (
        @(posedge clk) (q && !(i2 & i3)) |-> (i0 & i1)
    );

    // A low q implies the first AND term is low.
    check_q_low_implies_first_term_low: assert property (
        @(posedge clk) !q |-> !(i0 & i1)
    );

    // A low q implies the second AND term is low.
    check_q_low_implies_second_term_low: assert property (
        @(posedge clk) !q |-> !(i2 & i3)
    );

endmodule