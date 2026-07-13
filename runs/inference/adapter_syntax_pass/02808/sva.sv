module split_16bit_to_8bit_sva (
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo
);

    // out_hi is always the upper input byte.
    check_out_hi_matches_upper_byte: assert property (
        @($global_clock) out_hi == in[15:8]
    );

    // out_lo is always the lower input byte.
    check_out_lo_matches_lower_byte: assert property (
        @($global_clock) out_lo == in[7:0]
    );

    // The upper output byte is never zero.
    check_out_hi_nonzero: assert property (
        @($global_clock) out_hi != 8'h00
    );

    // The lower output byte is never zero.
    check_out_lo_nonzero: assert property (
        @($global_clock) out_lo != 8'h00
    );

    // The upper output byte is always even.
    check_out_hi_even: assert property (
        @($global_clock) out_hi[0] == 1'b0
    );

    // The lower output byte is always even.
    check_out_lo_even: assert property (
        @($global_clock) out_lo[0] == 1'b0
    );

    // The upper output byte is always in the range 0x20 to 0x7E.
    check_out_hi_range: assert property (
        @($global_clock) (out_hi >= 8'h20) && (out_hi <= 8'h7E)
    );

    // The lower output byte is always in the range 0x20 to 0x7E.
    check_out_lo_range: assert property (
        @($global_clock) (out_lo >= 8'h20) && (out_lo <= 8'h7E)
    );

endmodule