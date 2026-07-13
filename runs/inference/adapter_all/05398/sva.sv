module adder_16bit_signed_unsigned_sva (
    input logic CLK,
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic cin,
    input logic signed [15:0] sum,
    input logic cout
);
    // No clock/reset in RTL; combinational logic; assertions sample on CLK.

    // sum equals the selected add result (a+b or b+a) masked by sign bits.
    check_sum_selected_add: assert property (
        @(posedge CLK) sum == ((a[15] == b[15]) ? (a + b + cin) : ((a > b) ? (a + b) : (b + a)))
    );

    // cout equals the RTL carry equation using sign bits and truncated sum MSB.
    check_cout_equation: assert property (
        @(posedge CLK) cout == ((a[15] & b[15]) | ((a[15] | b[15]) & ~((a + b + cin)[15])))
    );

    // When signs match, sum equals the unsigned addition result.
    check_sum_when_signs_match: assert property (
        @(posedge CLK) (a[15] == b[15]) |-> (sum == (a + b + cin))
    );

    // When signs differ, sum equals the larger absolute value plus cin.
    check_sum_when_signs_differ: assert property (
        @(posedge CLK) (a[15] != b[15]) |-> (sum == ((a > b) ? (a + b) : (b + a)))
    );

    // When signs differ and a > b, sum equals a + b.
    check_sum_when_signs_differ_a_gt_b: assert property (
        @(posedge CLK) (a[15] != b[15] && a > b) |-> (sum == (a + b))
    );

    // When signs differ and b > a, sum equals b + a.
    check_sum_when_signs_differ_b_gt_a: assert property (
        @(posedge CLK) (a[15] != b[15] && b > a) |-> (sum == (b + a))
    );

    // cout is 0 when both inputs are non-negative.
    check_cout_zero_when_both_nonneg: assert property (
        @(posedge CLK) (a[15] == 1'b0 && b[15] == 1'b0) |-> (cout == 1'b0)
    );

    // cout is 0 when both inputs are non-positive.
    check_cout_zero_when_both_nonpos: assert property (
        @(posedge CLK) (a[15] == 1'b1 && b[15] == 1'b1) |-> (cout == 1'b0)
    );

    // cout is 1 when inputs have opposite signs and truncated sum is negative.
    check_cout_one_when_signs_diff_and_sum_neg: assert property (
        @(posedge CLK) (a[15] != b[15] && ((a + b + cin)[15] == 1'b1)) |-> (cout == 1'b1)
    );

    // cout is 1 when inputs have opposite signs and truncated sum is non-negative.
    check_cout_one_when_signs_diff_and_sum_nonneg: assert property (
        @(posedge CLK) (a[15] != b[15] && ((a + b + cin)[15] == 1'b0)) |-> (cout == 1'b1)
    );

    // sum is always non-negative (masked by sign bits).
    check_sum_nonnegative: assert property (
        @(posedge CLK) sum[15] == 1'b0
    );

endmodule