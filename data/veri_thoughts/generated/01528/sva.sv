module arithmetic_8bit_sva (
    input logic CLK,
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic sel,
    input logic signed [7:0] Y
);
    typedef logic signed [7:0] s8_t;

    // When sel==0, Y is A + B (8-bit signed wrap).
    check_sum_branch: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (Y == s8_t'(A + B))
    );

    // When sel==1, Y is A - B (8-bit signed wrap).
    check_diff_branch: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (Y == s8_t'(A - B))
    );

    // For addition branch, if B==0 then Y==A.
    check_sum_identity_B_zero: assert property (
        @(posedge CLK) (sel == 1'b0 && (B == 8'sd0)) |-> (Y == A)
    );

    // For addition branch, if A==0 then Y==B.
    check_sum_identity_A_zero: assert property (
        @(posedge CLK) (sel == 1'b0 && (A == 8'sd0)) |-> (Y == B)
    );

    // For subtraction branch, if B==0 then Y==A.
    check_diff_identity_B_zero: assert property (
        @(posedge CLK) (sel == 1'b1 && (B == 8'sd0)) |-> (Y == A)
    );

    // For subtraction branch, if A==B then Y==0.
    check_diff_self_sub_zero: assert property (
        @(posedge CLK) (sel == 1'b1 && (A == B)) |-> (Y == 8'sd0)
    );

    // For addition branch, if B == -A (8-bit) then Y==0.
    check_sum_negation_zero: assert property (
        @(posedge CLK) (sel == 1'b0 && (B == s8_t'(-A))) |-> (Y == 8'sd0)
    );

    // For addition branch, reversing: (Y - B) == A (8-bit).
    check_sum_reverse_relation: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (s8_t'(Y - B) == A)
    );

    // For subtraction branch, reversing: (Y + B) == A (8-bit).
    check_diff_reverse_relation: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (s8_t'(Y + B) == A)
    );

    // If A,B,sel are stable, Y must be stable (combinational determinism).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate) $stable({A,B,sel}) |-> $stable(Y)
    );

endmodule