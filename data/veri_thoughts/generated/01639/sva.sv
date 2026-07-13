module U2_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] OUT
);

    // OUT equals absolute difference of A and B.
    check_abs_difference_function: assert property (
        @(posedge CLK) OUT == ((A >= B) ? (A - B) : (B - A))
    );

    // When A >= B, OUT equals A - B.
    check_case_A_ge_B: assert property (
        @(posedge CLK) (A >= B) |-> (OUT == (A - B))
    );

    // When A < B, OUT equals B - A.
    check_case_B_gt_A: assert property (
        @(posedge CLK) (A < B) |-> (OUT == (B - A))
    );

    // Equal inputs produce zero output.
    check_equal_inputs_zero_out: assert property (
        @(posedge CLK) (A == B) |-> (OUT == 8'd0)
    );

    // Zero output implies inputs are equal.
    check_zero_out_implies_equal: assert property (
        @(posedge CLK) (OUT == 8'd0) |-> (A == B)
    );

    // If B is zero, OUT equals A.
    check_B_zero_out_eq_A: assert property (
        @(posedge CLK) (B == 8'd0) |-> (OUT == A)
    );

    // If A is zero, OUT equals B.
    check_A_zero_out_eq_B: assert property (
        @(posedge CLK) (A == 8'd0) |-> (OUT == B)
    );

    // Result never exceeds A when A >= B.
    check_out_le_max_when_A_ge_B: assert property (
        @(posedge CLK) (A >= B) |-> (OUT <= A)
    );

    // Result never exceeds B when A < B.
    check_out_le_max_when_B_gt_A: assert property (
        @(posedge CLK) (A < B) |-> (OUT <= B)
    );

    // Min plus OUT equals max.
    check_min_plus_out_equals_max: assert property (
        @(posedge CLK) ((A >= B) ? ((OUT + B) == A) : ((OUT + A) == B))
    );

    // OUT equals one of the two directed differences.
    check_out_is_one_of_two_diffs: assert property (
        @(posedge CLK) (OUT == (A - B)) || (OUT == (B - A))
    );

endmodule