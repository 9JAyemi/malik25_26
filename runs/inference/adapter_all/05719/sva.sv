module and_gate_extra_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must match the implemented AND-with-inverted-C function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == (A & B & ~C)
    );

    // Y can be high only when A, B, and inverted C are all high.
    check_y_high_requires_inputs: assert property (
        @(posedge clk) Y |-> (A && B && !C)
    );

    // With inverted C high, Y must be low.
    check_y_low_when_c_inverted: assert property (
        @(posedge clk) !C |-> !Y
    );

    // With A and B high, Y must equal inverted C.
    check_y_equals_not_c_when_ab_high: assert property (
        @(posedge clk) (A && B) |-> (Y == ~C)
    );

    // With inverted C low, Y must equal A AND B.
    check_y_equals_ab_when_c_not_inverted: assert property (
        @(posedge clk) !C |-> (Y == (A & B))
    );

    // With inverted C high and B high, Y must equal A.
    check_y_equals_a_when_c_inverted_and_b_high: assert property (
        @(posedge clk) (!C && B) |-> (Y == A)
    );

    // With inverted C high and A high, Y must equal B.
    check_y_equals_b_when_c_inverted_and_a_high: assert property (
        @(posedge clk) (!C && A) |-> (Y == B)
    );

    // With inverted C low and B low, Y must be low.
    check_y_low_when_c_not_inverted_and_b_low: assert property (
        @(posedge clk) (!C && !B) |-> !Y
    );

    // With inverted C low and A low, Y must be low.
    check_y_low_when_c_not_inverted_and_a_low: assert property (
        @(posedge clk) (!C && !A) |-> !Y
    );

endmodule