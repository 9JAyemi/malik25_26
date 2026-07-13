module decoder_4to16_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EN,
    input logic [15:0] Y
);

    // When disabled, the output must be all ones.
    check_disabled_all_ones: assert property (
        @($global_clock) (!EN) |-> (Y == 16'hFFFF)
    );

    // When A is nonzero, the default branch must drive all ones.
    check_a_nonzero_all_ones: assert property (
        @($global_clock) (EN && (A != 2'b00)) |-> (Y == 16'hFFFF)
    );

    // A=00, B=00, EN=1 selects bit 0 low.
    check_decode_b00: assert property (
        @($global_clock) (EN && (A == 2'b00) && (B == 2'b00)) |-> (Y == 16'hFFFE)
    );

    // A=00, B=01, EN=1 selects bit 1 low.
    check_decode_b01: assert property (
        @($global_clock) (EN && (A == 2'b00) && (B == 2'b01)) |-> (Y == 16'hFFFD)
    );

    // A=00, B=10, EN=1 selects bit 2 low.
    check_decode_b10: assert property (
        @($global_clock) (EN && (A == 2'b00) && (B == 2'b10)) |-> (Y == 16'hFFFB)
    );

    // A=00, B=11, EN=1 selects bit 3 low.
    check_decode_b11: assert property (
        @($global_clock) (EN && (A == 2'b00) && (B == 2'b11)) |-> (Y == 16'hFFF7)
    );

    // The upper 12 output bits are always high.
    check_upper_bits_always_high: assert property (
        @($global_clock) (Y[15:4] == 12'hFFF)
    );

    // With EN high and A zero, the low nibble must be one of the four implemented patterns.
    check_enabled_low_nibble_patterns: assert property (
        @($global_clock) (EN && (A == 2'b00)) |-> (
            (Y[3:0] == 4'b1110) ||
            (Y[3:0] == 4'b1101) ||
            (Y[3:0] == 4'b1011) ||
            (Y[3:0] == 4'b0111)
        )
    );

    // Any output other than all ones requires EN high and A zero.
    check_nondefault_output_requires_enable_and_a_zero: assert property (
        @($global_clock) (Y != 16'hFFFF) |-> (EN && (A == 2'b00))
    );

    // Any nondefault output must match the implemented B decode.
    check_nondefault_output_matches_b: assert property (
        @($global_clock) (Y != 16'hFFFF) |-> (
            ((Y == 16'hFFFE) && (B == 2'b00)) ||
            ((Y == 16'hFFFD) && (B == 2'b01)) ||
            ((Y == 16'hFFFB) && (B == 2'b10)) ||
            ((Y == 16'hFFF7) && (B == 2'b11))
        )
    );

endmodule