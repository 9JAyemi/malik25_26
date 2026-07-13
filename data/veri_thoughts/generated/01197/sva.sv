module sky130_fd_sc_lp__a2bb2oi_sva (
    input logic CLK,   // external sampling clock for combinational DUT
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    // Y equals (A1_N & A2_N) OR (B1 & B2).
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ((A1_N & A2_N) | (B1 & B2))
    );

    // If A1_N&A2_N are HIGH, Y must be HIGH.
    check_y_high_when_a_pair_true: assert property (
        @(posedge CLK) disable iff (1'b0) (A1_N & A2_N) |-> (Y == 1'b1)
    );

    // If B1&B2 are HIGH, Y must be HIGH.
    check_y_high_when_b_pair_true: assert property (
        @(posedge CLK) disable iff (1'b0) (B1 & B2) |-> (Y == 1'b1)
    );

    // If both pairs are FALSE, Y must be LOW.
    check_y_low_when_both_pairs_false: assert property (
        @(posedge CLK) disable iff (1'b0) (~(A1_N & A2_N) && ~(B1 & B2)) |-> (Y == 1'b0)
    );

    // If Y is LOW, both pairs must be FALSE.
    check_y_low_implies_both_pairs_false: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b0) |-> (~(A1_N & A2_N) && ~(B1 & B2))
    );

    // If Y is HIGH, at least one pair must be TRUE.
    check_y_high_implies_some_pair_true: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b1) |-> ((A1_N & A2_N) || (B1 & B2))
    );

    // When B pair is FALSE, Y equals A1_N&A2_N.
    check_reduce_to_a_when_b_false: assert property (
        @(posedge CLK) disable iff (1'b0) (~(B1 & B2)) |-> (Y == (A1_N & A2_N))
    );

    // When A pair is FALSE, Y equals B1&B2.
    check_reduce_to_b_when_a_false: assert property (
        @(posedge CLK) disable iff (1'b0) (~(A1_N & A2_N)) |-> (Y == (B1 & B2))
    );

    // If exactly one pair is TRUE, Y must be HIGH.
    check_y_high_when_exactly_one_pair_true: assert property (
        @(posedge CLK) disable iff (1'b0) ((A1_N & A2_N) ^ (B1 & B2)) |-> (Y == 1'b1)
    );

    // If both pairs are TRUE, Y must be HIGH.
    check_y_high_when_both_pairs_true: assert property (
        @(posedge CLK) disable iff (1'b0) ((A1_N & A2_N) && (B1 & B2)) |-> (Y == 1'b1)
    );
endmodule