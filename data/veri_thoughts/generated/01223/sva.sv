module and_gate_sva (
    // DUT ports
    input logic A,
    input logic B,
    input logic Y
);
    // Analysis:
    // - No clock or reset in DUT; purely combinational logic.
    // - Key behavior: Y is the logical AND of A and B (Y = A & B).
    // - Assertions are sampled on any edge of A or B.

    ///// Combinational correctness /////
    // Y must always equal A & B.
    check_y_equals_and: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (Y == (A & B))
    );

    // If A is LOW, Y must be LOW.
    check_y_low_when_a_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!A) |-> (Y == 1'b0)
    );

    // If B is LOW, Y must be LOW.
    check_y_low_when_b_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!B) |-> (Y == 1'b0)
    );

    // Y can be HIGH only when both A and B are HIGH.
    check_y_high_implies_both_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1))
    );

    // If not both inputs are HIGH, Y must be LOW.
    check_not_both_high_implies_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (!(A && B)) |-> (Y == 1'b0)
    );

endmodule