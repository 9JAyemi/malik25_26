module binary_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [4:0] sum
);

    // Sum places the 4-bit a+b+c result in bits [4:1] and drives bit [0] low.
    check_sum_encoding: assert property (
        @(posedge clk) sum == {(a + b + c), 1'b0}
    );

    // Output bit 0 is always zero.
    check_sum_lsb_zero: assert property (
        @(posedge clk) sum[0] == 1'b0
    );

    // Output bits [4:1] match the truncated 4-bit addition result.
    check_sum_upper_bits: assert property (
        @(posedge clk) sum[4:1] == (a + b + c)
    );

    // If inputs are unchanged across samples, the output is unchanged too.
    check_output_stable_for_stable_inputs: assert property (
        @(posedge clk) $stable({a, b, c}) |-> $stable(sum)
    );

endmodule