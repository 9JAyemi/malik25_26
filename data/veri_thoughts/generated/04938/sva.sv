module decoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [15:0] out
);

    // Output matches the decoded input value.
    check_exact_decode: assert property (
        @(posedge clk) out == (16'h0001 << in)
    );

    // Exactly one output bit is asserted.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // The selected output bit is high.
    check_selected_bit_high: assert property (
        @(posedge clk) out[in] == 1'b1
    );

    // All non-selected output bits are low.
    check_unselected_bits_low: assert property (
        @(posedge clk) (out & ~(16'h0001 << in)) == 16'h0000
    );

endmodule