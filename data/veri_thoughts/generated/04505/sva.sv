module half_subtractor_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic DIFF,
    input logic BORROW
);

    // DIFF is the XOR of A and B.
    check_diff_is_xor: assert property (
        @(posedge clk) disable iff (1'b0)
        DIFF == (A ^ B)
    );

    // BORROW matches the single-bit less-than result.
    check_borrow_is_less_than: assert property (
        @(posedge clk) disable iff (1'b0)
        BORROW == (A < B)
    );

    // When B is low, DIFF follows A and BORROW stays low.
    check_b_zero_behavior: assert property (
        @(posedge clk) disable iff (1'b0)
        !B |-> ((DIFF == A) && (BORROW == 1'b0))
    );

    // Subtracting 1 from 0 produces DIFF high with BORROW high.
    check_zero_minus_one_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A && B) |-> ((DIFF == 1'b1) && (BORROW == 1'b1))
    );

endmodule

module full_subtractor_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic BORROW_IN,
    input logic DIFF,
    input logic BORROW
);

    // DIFF is the cascaded XOR of A, B, and BORROW_IN.
    check_diff_is_three_input_xor: assert property (
        @(posedge clk) disable iff (1'b0)
        DIFF == (A ^ B ^ BORROW_IN)
    );

    // BORROW is the OR of the two half-subtractor borrow terms.
    check_borrow_matches_composed_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        BORROW == ((A < B) | ((A ^ B) < BORROW_IN))
    );

    // With no borrow-in, behavior reduces to subtracting B from A.
    check_no_borrow_in_reduces_to_half_subtractor: assert property (
        @(posedge clk) disable iff (1'b0)
        !BORROW_IN |-> ((DIFF == (A ^ B)) && (BORROW == (A < B)))
    );

    // With B low, behavior reduces to subtracting BORROW_IN from A.
    check_b_zero_reduces_to_a_minus_borrow_in: assert property (
        @(posedge clk) disable iff (1'b0)
        !B |-> ((DIFF == (A ^ BORROW_IN)) && (BORROW == (!A && BORROW_IN)))
    );

    // When A is low and B is high, a borrow is always generated.
    check_zero_minus_one_always_borrows: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A && B) |-> (BORROW == 1'b1)
    );

endmodule