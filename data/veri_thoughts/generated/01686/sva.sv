module add16_sva (
    input logic [15:0] a,
    input logic [15:0] b,
    input logic        cin,
    input logic [15:0] sum,
    input logic        cout
);
    // Outputs equal 17-bit sum of a + (b<<1) + cin.
    check_result_17bit_sum: assert property (
        @(posedge cin) {cout, sum} == ({1'b0, a} + {b, 1'b0} + cin)
    );

    // Outputs equal truncated original expression from RTL.
    check_result_original_expr: assert property (
        @(posedge cin) {cout, sum} == (({1'b0, a} + {1'b0, b, cin})[16:0])
    );

    // LSB of sum equals a[0] XOR cin (since 2*b has LSB 0).
    check_sum_lsb_xor: assert property (
        @(posedge cin) sum[0] == (a[0] ^ cin)
    );

    // If b is zero, result is a plus cin in 17 bits.
    check_b_zero_behavior: assert property (
        @(posedge cin) (b == 16'h0000) |-> ({cout, sum} == ({1'b0, a} + cin))
    );

    // If a is zero, result is (b<<1) plus cin in 17 bits.
    check_a_zero_behavior: assert property (
        @(posedge cin) (a == 16'h0000) |-> ({cout, sum} == ({b, 1'b0} + cin))
    );

    // If a and b are zero, cout must be 0 regardless of cin.
    check_ab_zero_cout_zero: assert property (
        @(posedge cin) (a == 16'h0000 && b == 16'h0000) |-> (cout == 1'b0)
    );

    // If a is zero and b's MSB is set, cout must be 1 regardless of cin.
    check_a_zero_bmsb_sets_cout: assert property (
        @(posedge cin) (a == 16'h0000 && b == 16'h8000) |-> (cout == 1'b1)
    );

    // If a is zero and b's MSB is clear, cout must be 0 regardless of cin.
    check_a_zero_bmsb_clear_cout_zero: assert property (
        @(posedge cin) (a == 16'h0000 && b[15] == 1'b0) |-> (cout == 1'b0)
    );

    // cout==1 implies 17-bit sum is at least 2^16.
    check_cout_implies_threshold: assert property (
        @(posedge cin) (cout == 1'b1) |-> (({1'b0, a} + {b, 1'b0} + cin) >= 17'h1_0000)
    );

    // cout==0 implies 17-bit sum is less than 2^16.
    check_no_cout_implies_below_threshold: assert property (
        @(posedge cin) (cout == 1'b0) |-> (({1'b0, a} + {b, 1'b0} + cin) < 17'h1_0000)
    );
endmodule