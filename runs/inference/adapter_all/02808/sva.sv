module split_16bit_to_8bit_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_hi is always the upper byte of the input.
    check_out_hi_matches_upper_byte: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // out_lo is always the lower byte of the input.
    check_out_lo_matches_lower_byte: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // The upper output byte is never affected by the upper input nibble.
    check_out_hi_ignores_upper_select: assert property (
        @(posedge clk) (in[15:14] == 2'b00) |-> (out_hi == in[15:8])
    );

    // The lower output byte is never affected by the lower input nibble.
    check_out_lo_ignores_lower_select: assert property (
        @(posedge clk) (in[13:12] == 2'b00) |-> (out_lo == in[7:0])
    );

    // With both nibbles at zero, the upper output byte is zero.
    check_out_hi_zero_when_upper_select_zero: assert property (
        @(posedge clk) (in[15:14] == 2'b00) |-> (out_hi == 8'h00)
    );

    // With both nibbles at zero, the lower output byte is zero.
    check_out_lo_zero_when_lower_select_zero: assert property (
        @(posedge clk) (in[13:12] == 2'b00) |-> (out_lo == 8'h00)
    );

    // With both nibbles at one, the upper output byte is zero.
    check_out_hi_zero_when_upper_select_one: assert property (
        @(posedge clk) (in[15:14] == 2'b11) |-> (out_hi == 8'h00)
    );

    // With both nibbles at one, the lower output byte is zero.
    check_out_lo_zero_when_lower_select_one: assert property (
        @(posedge clk) (in[13:12] == 2'b11) |-> (out_lo == 8'h00)
    );

endmodule