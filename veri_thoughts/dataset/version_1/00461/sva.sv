module adder_sva (
    input logic clk,
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic signed [7:0] sum,
    input logic C
);

    // sum reflects the 8-bit signed addition of A and B.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (A + B)
    );

    // C is the sign-extension bit of the 8-bit result.
    check_c_matches_sum_sign: assert property (
        @(posedge clk) C == sum[7]
    );

    // With A equal to zero, the outputs mirror B.
    check_zero_left_identity: assert property (
        @(posedge clk) (A == 8'sd0) |-> ((sum == B) && (C == B[7]))
    );

    // With B equal to zero, the outputs mirror A.
    check_zero_right_identity: assert property (
        @(posedge clk) (B == 8'sd0) |-> ((sum == A) && (C == A[7]))
    );

    // Zero plus zero produces a zero result and clear C.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 8'sd0) && (B == 8'sd0)) |-> ((sum == 8'sd0) && (C == 1'b0))
    );

endmodule