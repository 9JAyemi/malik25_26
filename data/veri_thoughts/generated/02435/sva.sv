module nand4_sva (
    input logic CLK,  // External clock for sampling assertions (DUT is combinational)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y equals (~(A & B)) & (~(C & D)).
    check_function_and_of_pairwise_nand: assert property (
        @(posedge CLK) Y == ((~(A & B)) & (~(C & D)))
    );

    // Y equals ~((A & B) | (C & D)).
    check_function_not_or_of_pairwise_and: assert property (
        @(posedge CLK) Y == ~((A & B) | (C & D))
    );

    // If A and B are both 1, Y must be 0.
    check_y_low_if_ab_both_one: assert property (
        @(posedge CLK) (A && B) |-> (Y == 1'b0)
    );

    // If C and D are both 1, Y must be 0.
    check_y_low_if_cd_both_one: assert property (
        @(posedge CLK) (C && D) |-> (Y == 1'b0)
    );

    // Y is 1 only if neither pair (A,B) nor (C,D) are both 1.
    check_y_high_only_if_no_pair_is_11: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (!(A && B) && !(C && D))
    );

    // If neither pair (A,B) nor (C,D) are both 1, Y must be 1.
    check_y_high_when_no_pair_is_11: assert property (
        @(posedge CLK) (!(A && B) && !(C && D)) |-> (Y == 1'b1)
    );

    // If A is 0, Y equals ~(C & D).
    check_y_equals_nand_cd_if_a_zero: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == ~(C & D))
    );

    // If B is 0, Y equals ~(C & D).
    check_y_equals_nand_cd_if_b_zero: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == ~(C & D))
    );

    // If C is 0, Y equals ~(A & B).
    check_y_equals_nand_ab_if_c_zero: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == ~(A & B))
    );

    // If D is 0, Y equals ~(A & B).
    check_y_equals_nand_ab_if_d_zero: assert property (
        @(posedge CLK) (D == 1'b0) |-> (Y == ~(A & B))
    );
endmodule