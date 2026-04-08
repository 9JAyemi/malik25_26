module split_16bit_input_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_lo always reflects the low byte of the input.
    check_out_lo_matches_low_byte: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // out_hi selects the high byte only when in[15] is set.
    check_out_hi_matches_selected_byte: assert property (
        @(posedge clk) out_hi == (in[15] ? in[15:8] : in[7:0])
    );

    // When the input MSB is clear, both outputs equal the low byte.
    check_msb_clear_copies_low_byte_to_both_outputs: assert property (
        @(posedge clk) (in[15] == 1'b0) |-> ((out_hi == in[7:0]) && (out_lo == in[7:0]))
    );

    // When the input MSB is set, the outputs split into high and low bytes.
    check_msb_set_splits_high_and_low_bytes: assert property (
        @(posedge clk) (in[15] == 1'b1) |-> ((out_hi == in[15:8]) && (out_lo == in[7:0]))
    );

    // With a clear input MSB, the two outputs must match.
    check_outputs_equal_when_msb_clear: assert property (
        @(posedge clk) (in[15] == 1'b0) |-> (out_hi == out_lo)
    );

endmodule