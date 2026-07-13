module two_bit_comparator_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic Y
);
    // Y must be 1 when A > B.
    check_y_high_when_a_gt_b: assert property (
        @(posedge CLK) (A > B) |-> (Y == 1'b1)
    );

    // Y must be 0 when A <= B.
    check_y_low_when_a_le_b: assert property (
        @(posedge CLK) (A <= B) |-> (Y == 1'b0)
    );

    // If Y is 1 then A must be greater than B.
    check_y1_implies_a_gt_b: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (A > B)
    );

    // If MSBs differ and A[1]=1,B[1]=0 then Y must be 1.
    check_msb_diff_a1_b0: assert property (
        @(posedge CLK) (A[1] && !B[1]) |-> (Y == 1'b1)
    );

    // If MSBs differ and A[1]=0,B[1]=1 then Y must be 0.
    check_msb_diff_a0_b1: assert property (
        @(posedge CLK) (!A[1] && B[1]) |-> (Y == 1'b0)
    );

    // If MSBs equal, comparison reduces to LSB: Y == (A[0] & ~B[0]).
    check_msb_equal_lsb_decides: assert property (
        @(posedge CLK) (A[1] == B[1]) |-> (Y == (A[0] & ~B[0]))
    );

    // If A equals B then Y must be 0.
    check_equal_inputs_y0: assert property (
        @(posedge CLK) (A == B) |-> (Y == 1'b0)
    );

    // If A is 0 then Y must be 0.
    check_a_zero_y0: assert property (
        @(posedge CLK) (A == 2'b00) |-> (Y == 1'b0)
    );

    // If B is 3 then Y must be 0.
    check_b_three_y0: assert property (
        @(posedge CLK) (B == 2'b11) |-> (Y == 1'b0)
    );

    // If A is 3 and B is not 3 then Y must be 1.
    check_a_three_gt_non_three: assert property (
        @(posedge CLK) (A == 2'b11 && B != 2'b11) |-> (Y == 1'b1)
    );
endmodule