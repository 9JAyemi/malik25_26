module logic_operation_sva (
    input  logic clk, // sampling clock for assertions
    input  logic Y,
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic D
);
    // DUT is pure combinational: Y == (A & B) | (C & D); no reset present.

    // Y equals (A&B)|(C&D) every sampled cycle.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ((A && B) || (C && D))
    );

    // If A and B are both HIGH, Y must be HIGH the same cycle.
    check_y_high_when_ab_true: assert property (
        @(posedge clk) (A && B) |-> (Y == 1'b1)
    );

    // If C and D are both HIGH, Y must be HIGH the same cycle.
    check_y_high_when_cd_true: assert property (
        @(posedge clk) (C && D) |-> (Y == 1'b1)
    );

    // If neither pair (A&B) nor (C&D) is HIGH, Y must be LOW.
    check_y_low_when_no_pair_true: assert property (
        @(posedge clk) (!(A && B) && !(C && D)) |-> (Y == 1'b0)
    );

    // If Y is HIGH, at least one pair (A&B) or (C&D) must be HIGH.
    check_y_high_implies_pair_true: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A && B) || (C && D))
    );

    // If Y is LOW, neither (A&B) nor (C&D) is HIGH.
    check_y_low_implies_no_pair_true: assert property (
        @(posedge clk) (Y == 1'b0) |-> (!(A && B) && !(C && D))
    );
endmodule