module top_module_sva(
    input logic        clk,
    input logic [31:0] in,
    input logic [31:0] out_xor,
    input logic [31:0] out_and
);

    // out_xor must be the zero-extended XOR of the two 16-bit input halves.
    check_out_xor_value: assert property (
        @(posedge clk) out_xor == {16'h0000, (in[31:16] ^ in[15:0])}
    );

    // out_and must be the zero-extended AND of the two 16-bit input halves.
    check_out_and_value: assert property (
        @(posedge clk) out_and == {16'h0000, (in[31:16] & in[15:0])}
    );

    // The upper 16 bits of out_xor must be zero.
    check_out_xor_upper_zero: assert property (
        @(posedge clk) out_xor[31:16] == 16'h0000
    );

    // The upper 16 bits of out_and must be zero.
    check_out_and_upper_zero: assert property (
        @(posedge clk) out_and[31:16] == 16'h0000
    );

    // The lower 16 bits of out_xor must match the XOR result.
    check_out_xor_lower_bits: assert property (
        @(posedge clk) out_xor[15:0] == (in[31:16] ^ in[15:0])
    );

    // The lower 16 bits of out_and must match the AND result.
    check_out_and_lower_bits: assert property (
        @(posedge clk) out_and[15:0] == (in[31:16] & in[15:0])
    );

endmodule