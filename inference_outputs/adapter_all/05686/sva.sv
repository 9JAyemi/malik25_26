module sky130_fd_sc_hs__a222o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

    // X must match the implemented OR-of-terms function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (((A1 & A2) | (B1 & B2) | (~C1 & ~C2)) ? 1'b1 : 1'b0)
    );

    // X must be high when the first product term is true.
    check_x_high_on_a_term: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // X must be high when the second product term is true.
    check_x_high_on_b_term: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // X must be high when the third product term is true.
    check_x_high_on_c_term: assert property (
        @(posedge clk) (~C1 & ~C2) |-> X
    );

    // X must be low when all three product terms are false.
    check_x_low_when_no_terms: assert property (
        @(posedge clk) !(A1 & A2 && B1 & B2 && ~C1 & ~C2) |-> !X
    );

    // X must be low when the first and second product terms are false.
    check_x_low_when_a_and_b_terms_false: assert property (
        @(posedge clk) !(A1 & A2 && B1 & B2) |-> !X
    );

    // X must be low when the first and third product terms are false.
    check_x_low_when_a_and_c_terms_false: assert property (
        @(posedge clk) !(A1 & A2 && ~C1 & ~C2) |-> !X
    );

    // X must be low when the second and third product terms are false.
    check_x_low_when_b_and_c_terms_false: assert property (
        @(posedge clk) !(B1 & B2 && ~C1 & ~C2) |-> !X
    );

    // X must be high when the first and second product terms are true.
    check_x_high_when_a_and_b_terms_true: assert property (
        @(posedge clk) (A1 & A2 && B1 & B2) |-> X
    );

    // X must be high when the first and third product terms are true.
    check_x_high_when_a_and_c_terms_true: assert property (
        @(posedge clk) (A1 & A2 && ~C1 & ~C2) |-> X
    );

    // X must be high when the second and third product terms are true.
    check_x_high_when_b_and_c_terms_true: assert property (
        @(posedge clk) (B1 & B2 && ~C1 & ~C2) |-> X
    );

endmodule