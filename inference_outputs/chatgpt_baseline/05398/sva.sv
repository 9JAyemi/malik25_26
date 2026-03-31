module adder_16bit_signed_unsigned_sva (
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic cin,
    input logic signed [15:0] sum,
    input logic cout
);

    wire [15:0] unsigned_sum;

    assign unsigned_sum = a + b + cin;

    // sum matches the RTL ternary expression.
    check_sum_definition: assert property (
        @($global_clock)
        sum == ((a[15] == b[15]) ? unsigned_sum : ((a > b) ? (a + b) : (b + a)))
    );

    // Same-sign inputs drive sum from unsigned_sum.
    check_sum_same_sign_uses_unsigned_sum: assert property (
        @($global_clock)
        (a[15] == b[15]) |-> (sum == unsigned_sum)
    );

    // Mixed-sign inputs with a greater than b select a+b.
    check_sum_mixed_sign_a_gt_b_branch: assert property (
        @($global_clock)
        ((a[15] != b[15]) && (a > b)) |-> (sum == (a + b))
    );

    // Mixed-sign inputs with a not greater than b select b+a.
    check_sum_mixed_sign_b_ge_a_branch: assert property (
        @($global_clock)
        ((a[15] != b[15]) && !(a > b)) |-> (sum == (b + a))
    );

    // cout matches the RTL sign-based expression.
    check_cout_definition: assert property (
        @($global_clock)
        cout == ((a[15] & b[15]) | ((a[15] | b[15]) & ~unsigned_sum[15]))
    );

    // Two non-negative inputs force cout low.
    check_cout_low_for_non_negative_inputs: assert property (
        @($global_clock)
        (!a[15] && !b[15]) |-> (cout == 1'b0)
    );

    // Two negative inputs force cout high.
    check_cout_high_for_negative_inputs: assert property (
        @($global_clock)
        (a[15] && b[15]) |-> (cout == 1'b1)
    );

    // Mixed-sign inputs with a low unsigned_sum MSB force cout high.
    check_cout_high_for_mixed_sign_low_msb: assert property (
        @($global_clock)
        ((a[15] ^ b[15]) && !unsigned_sum[15]) |-> (cout == 1'b1)
    );

    // Mixed-sign inputs with a high unsigned_sum MSB force cout low.
    check_cout_low_for_mixed_sign_high_msb: assert property (
        @($global_clock)
        ((a[15] ^ b[15]) && unsigned_sum[15]) |-> (cout == 1'b0)
    );

endmodule