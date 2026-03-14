module ones_complement_sva (
    input logic clk,          // sampling clock (DUT has no clock/reset)
    input logic [3:0] in,
    input logic [3:0] out
);

    // out equals bitwise NOT of in.
    check_out_equals_bitwise_not_in: assert property (
        @(posedge clk) out == ~in
    );

    // out XOR in is all ones.
    check_xor_all_ones: assert property (
        @(posedge clk) (out ^ in) == 4'hF
    );

    // out OR in is all ones.
    check_or_all_ones: assert property (
        @(posedge clk) (out | in) == 4'hF
    );

    // out AND in is all zeros.
    check_and_all_zeros: assert property (
        @(posedge clk) (out & in) == 4'h0
    );

    // Bit 0 is complemented.
    check_bit0_complement: assert property (
        @(posedge clk) out[0] == ~in[0]
    );

    // Bit 1 is complemented.
    check_bit1_complement: assert property (
        @(posedge clk) out[1] == ~in[1]
    );

    // Bit 2 is complemented.
    check_bit2_complement: assert property (
        @(posedge clk) out[2] == ~in[2]
    );

    // Bit 3 is complemented.
    check_bit3_complement: assert property (
        @(posedge clk) out[3] == ~in[3]
    );

    // out is never equal to in.
    check_never_equal: assert property (
        @(posedge clk) out != in
    );

endmodule