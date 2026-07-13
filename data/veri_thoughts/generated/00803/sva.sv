module adder32_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic cin,
    input logic [31:0] sum,
    input logic cout,
    input logic [15:0] a_low,
    input logic [15:0] b_low,
    input logic [15:0] sum_low,
    input logic [15:0] a_high,
    input logic [15:0] b_high,
    input logic [15:0] sum_high,
    input logic c1,
    input logic c2
);
    // a_low is the low 16 bits of a.
    check_a_low_slice: assert property (
        @(posedge CLK) a_low == a[15:0]
    );
    // b_low is the low 16 bits of b.
    check_b_low_slice: assert property (
        @(posedge CLK) b_low == b[15:0]
    );
    // a_high is the high 16 bits of a.
    check_a_high_slice: assert property (
        @(posedge CLK) a_high == a[31:16]
    );
    // b_high is the high 16 bits of b.
    check_b_high_slice: assert property (
        @(posedge CLK) b_high == b[31:16]
    );
    // Low 16-bit adder computes sum_low and carry c1.
    check_low_adder_function: assert property (
        @(posedge CLK) {c1, sum_low} == ({1'b0, a_low} + {1'b0, b_low} + cin)
    );
    // High 16-bit adder computes sum_high and carry c2 using c1 as carry-in.
    check_high_adder_function: assert property (
        @(posedge CLK) {c2, sum_high} == ({1'b0, a_high} + {1'b0, b_high} + c1)
    );
    // 32-bit sum is the concatenation of high and low sums.
    check_sum_concat: assert property (
        @(posedge CLK) sum == {sum_high, sum_low}
    );
    // cout equals the final carry c2.
    check_cout_equals_c2: assert property (
        @(posedge CLK) cout == c2
    );
    // sum_low matches low 16 bits of sum.
    check_sum_low_slice_match: assert property (
        @(posedge CLK) sum_low == sum[15:0]
    );
    // sum_high matches high 16 bits of sum.
    check_sum_high_slice_match: assert property (
        @(posedge CLK) sum_high == sum[31:16]
    );
    // Full 33-bit result equals a + b + cin.
    check_full_width_sum: assert property (
        @(posedge CLK) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );
endmodule