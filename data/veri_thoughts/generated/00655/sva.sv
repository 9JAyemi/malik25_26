module sky130_fd_sc_hdll__a32oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Use global formal clock since DUT is purely combinational.
    default clocking cb @(posedge $global_clock); endclocking

    // Y implements ~( (A1&A2&A3) | (B1&B2) ).
    check_function_equation: assert property (
        Y == ~((A1 & A2 & A3) | (B1 & B2))
    );

    // When both terms are FALSE, Y must be 1.
    check_y_one_when_terms_zero: assert property (
        (~(A1 & A2 & A3) && ~(B1 & B2)) |-> (Y == 1'b1)
    );

    // When A1&A2&A3 is TRUE, Y must be 0.
    check_y_zero_when_a_term_one: assert property (
        (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // When B1&B2 is TRUE, Y must be 0.
    check_y_zero_when_b_term_one: assert property (
        (B1 & B2) |-> (Y == 1'b0)
    );

    // If Y is 1, then both terms must be FALSE.
    check_y_one_implies_both_terms_zero: assert property (
        (Y == 1'b1) |-> (~(A1 & A2 & A3) && ~(B1 & B2))
    );

    // If Y is 0, then at least one term must be TRUE.
    check_y_zero_implies_some_term_one: assert property (
        (Y == 1'b0) |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // If A3 is 0, Y reduces to ~(B1&B2).
    check_reduce_when_a3_zero: assert property (
        (A3 == 1'b0) |-> (Y == ~(B1 & B2))
    );

    // If B2 is 0, Y reduces to ~(A1&A2&A3).
    check_reduce_when_b2_zero: assert property (
        (B2 == 1'b0) |-> (Y == ~(A1 & A2 & A3))
    );

    // If A1 and A2 are 1, Y reduces to ~(A3 | (B1&B2)).
    check_reduce_when_a1a2_one: assert property (
        (A1 && A2) |-> (Y == ~(A3 | (B1 & B2)))
    );

    // If B1 is 1, Y reduces to ~((A1&A2&A3) | B2).
    check_reduce_when_b1_one: assert property (
        (B1 == 1'b1) |-> (Y == ~((A1 & A2 & A3) | B2))
    );

endmodule