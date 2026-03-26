module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [6:0] seg
);

    // Upper output bits are zero-extended from a 4-bit result.
    check_seg_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset)
            seg[6:4] == 3'b000
    );

    // The output is always even.
    check_seg_lsb_zero: assert property (
        @(posedge clk) disable iff (reset)
            seg[0] == 1'b0
    );

    // Bit 1 matches the bit 0 sum of a+b.
    check_seg_bit1_matches_sum0: assert property (
        @(posedge clk) disable iff (reset)
            seg[1] == (a[0] ^ b[0])
    );

    // Bit 2 matches the bit 1 sum of a+b.
    check_seg_bit2_matches_sum1: assert property (
        @(posedge clk) disable iff (reset)
            seg[2] == (a[1] ^ b[1] ^ (a[0] & b[0]))
    );

    // Bit 3 matches the bit 2 sum of a+b.
    check_seg_bit3_matches_sum2: assert property (
        @(posedge clk) disable iff (reset)
            seg[3] == (a[2] ^ b[2] ^ ((a[1] & b[1]) | (a[1] & (a[0] & b[0])) | (b[1] & (a[0] & b[0]))))
    );

    // The full output matches the truncated double-sum implemented by the RTL.
    check_seg_matches_truncated_double_sum: assert property (
        @(posedge clk) disable iff (reset)
            seg == {3'b000, (({1'b0, a} + {1'b0, b}) << 1)}
    );

    // Zero inputs produce zero output.
    check_zero_inputs_give_zero_output: assert property (
        @(posedge clk) disable iff (reset)
            (a == 3'b000 && b == 3'b000) |-> (seg == 7'b0000000)
    );

    // Maximum inputs wrap to 12 because the final add is 4 bits wide.
    check_max_inputs_wrap_to_twelve: assert property (
        @(posedge clk) disable iff (reset)
            (a == 3'b111 && b == 3'b111) |-> (seg == 7'd12)
    );

    // Stable inputs keep the output stable across cycles.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) && (a == $past(a)) && (b == $past(b)) |-> (seg == $past(seg))
    );

    // Swapping operands preserves the output.
    check_swapped_operands_preserve_output: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) && (a == $past(b)) && (b == $past(a)) |-> (seg == $past(seg))
    );

endmodule