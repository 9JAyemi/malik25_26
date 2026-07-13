module and_gate_sva (
    input logic clk,   // External verification clock (RTL has no clock/reset)
    input logic A,
    input logic B,
    input logic Y
);
    // Y equals the bitwise AND of A and B.
    check_y_equals_and: assert property (
        @(posedge clk) (Y == (A & B))
    );

    // If A is 0, Y must be 0.
    check_zero_when_a_zero: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b0)
    );

    // If B is 0, Y must be 0.
    check_zero_when_b_zero: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // If both A and B are 1, Y must be 1.
    check_one_when_both_one: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

    // If Y is 1, then both A and B must be 1.
    check_y_one_implies_inputs_one: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A == 1'b1 && B == 1'b1)
    );

    // Any change on Y must be caused by a change on A or B.
    check_y_change_requires_input_change: assert property (
        @(posedge clk) $changed(Y) |-> ($changed(A) || $changed(B))
    );
endmodule