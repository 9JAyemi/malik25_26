module signed_adder_sva (
    input logic signed [15:0] in1,
    input logic signed [15:0] in2,
    input logic clk,
    input logic signed [16:0] out,
    input logic signed [16:0] sum
);

    // sum captures the prior cycle's wrapped 16-bit signed addition.
    check_sum_register_update: assert property (
        @(posedge clk)
        $past(1'b1) |-> (sum == $signed($past(in1) + $past(in2)))
    );

    // out reflects the registered addition result from the prior cycle.
    check_out_registered_addition: assert property (
        @(posedge clk)
        $past(1'b1) |-> (out == $signed($past(in1) + $past(in2)))
    );

    // out always mirrors the internal sum register.
    check_out_matches_sum: assert property (
        @(posedge clk)
        out == sum
    );

    // When sum is negative, out takes the concatenation branch.
    check_negative_branch: assert property (
        @(posedge clk)
        sum[16] |-> (out == {1'b1, sum[15:0]})
    );

    // When sum is non-negative, out takes the zero-extended low-16 branch.
    check_nonnegative_branch: assert property (
        @(posedge clk)
        !sum[16] |-> (out == {1'b0, sum[15:0]})
    );

    // sum is sign-extended from the 16-bit registered add result.
    check_sum_sign_extension: assert property (
        @(posedge clk)
        $past(1'b1) |-> (sum[16] == sum[15])
    );

    // out is also sign-extended once the first registered value exists.
    check_out_sign_extension: assert property (
        @(posedge clk)
        $past(1'b1) |-> (out[16] == out[15])
    );

endmodule