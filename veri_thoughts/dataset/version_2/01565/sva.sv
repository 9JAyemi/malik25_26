module compare_op_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);
    // Y implements absolute difference |A-B|.
    check_absdiff_definition: assert property (
        @(posedge A[0] or posedge B[0]) Y == ((A > B) ? (A - B) : (B - A))
    );

    // When A > B, Y equals A - B.
    check_Y_when_A_gt_B: assert property (
        @(posedge A[0] or posedge B[0]) (A > B) |-> (Y == (A - B))
    );

    // When A <= B, Y equals B - A.
    check_Y_when_A_le_B: assert property (
        @(posedge A[0] or posedge B[0]) !(A > B) |-> (Y == (B - A))
    );

    // When A == B, Y is zero.
    check_zero_when_equal: assert property (
        @(posedge A[0] or posedge B[0]) (A == B) |-> (Y == 4'd0)
    );

    // Y is zero only when A == B.
    check_zero_implies_equal: assert property (
        @(posedge A[0] or posedge B[0]) (Y == 4'd0) |-> (A == B)
    );

    // If A >= B, then B + Y equals A.
    check_add_inverse_when_A_ge_B: assert property (
        @(posedge A[0] or posedge B[0]) (A >= B) |-> ((B + Y) == A)
    );

    // If B >= A, then A + Y equals B.
    check_add_inverse_when_B_ge_A: assert property (
        @(posedge A[0] or posedge B[0]) (B >= A) |-> ((A + Y) == B)
    );

    // For A > B, Y does not exceed A.
    check_upper_bound_when_A_gt_B: assert property (
        @(posedge A[0] or posedge B[0]) (A > B) |-> (Y <= A)
    );

    // For A <= B, Y does not exceed B.
    check_upper_bound_when_A_le_B: assert property (
        @(posedge A[0] or posedge B[0]) !(A > B) |-> (Y <= B)
    );

    // If B is zero, Y equals A.
    check_B_zero_pass_through: assert property (
        @(posedge A[0] or posedge B[0]) (B == 4'd0) |-> (Y == A)
    );

    // If A is zero, Y equals B.
    check_A_zero_pass_through: assert property (
        @(posedge A[0] or posedge B[0]) (A == 4'd0) |-> (Y == B)
    );
endmodule