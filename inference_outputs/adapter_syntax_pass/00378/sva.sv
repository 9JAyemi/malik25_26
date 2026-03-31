module decoder_4to16_sva (
    input logic [3:0] in,
    input logic ena,
    input logic [15:0] out
);

    // Output is always either all ones or exactly one active low bit.
    check_out_onehot0: assert property (
        @($global_clock) $onehot0(out)
    );

    // When disabled, the output is all ones.
    check_disabled_all_ones: assert property (
        @($global_clock) !ena |-> (out == 16'hFFFF)
    );

    // When enabled, bit 0 is active low for input 0000.
    check_enabled_bit0_map: assert property (
        @($global_clock) ena && (in == 4'h0) |-> (out == 16'hFFE)
    );

    // When enabled, bit 1 is active low for input 0001.
    check_enabled_bit1_map: assert property (
        @($global_clock) ena && (in == 4'h1) |-> (out == 16'hFFD)
    );

    // When enabled, bit 2 is active low for input 0010.
    check_enabled_bit2_map: assert property (
        @($global_clock) ena && (in == 4'h2) |-> (out == 16'hFFB)
    );

    // When enabled, bit 3 is active low for input 0011.
    check_enabled_bit3_map: assert property (
        @($global_clock) ena && (in == 4'h3) |-> (out == 16'hFF7)
    );

    // When enabled, bit 4 is active low for input 0100.
    check_enabled_bit4_map: assert property (
        @($global_clock) ena && (in == 4'h4) |-> (out == 16'hFEF)
    );

    // When enabled, bit 5 is active low for input 0101.
    check_enabled_bit5_map: assert property (
        @($global_clock) ena && (in == 4'h5) |-> (out == 16'hFDF)
    );

    // When enabled, bit 6 is active low for input 0110.
    check_enabled_bit6_map: assert property (
        @($global_clock) ena && (in == 4'h6) |-> (out == 16'hFBF)
    );

    // When enabled, bit 7 is active low for input 0111.
    check_enabled_bit7_map: assert property (
        @($global_clock) ena && (in == 4'h7) |-> (out == 16'hF7F)
    );

    // When enabled, bit 8 is active low for input 1000.
    check_enabled_bit8_map: assert property (
        @($global_clock) ena && (in == 4'h8) |-> (out == 16h'FEF)
    );

    // When enabled, bit 9 is active low for input 1001.
    check_enabled_bit9_map: assert property (
        @($global_clock) ena && (in == 4'h9) |-> (out == 16h'FDF)
    );

    // When enabled, bit 10 is active low for input 1010.
    check_enabled_bit10_map: assert property (
        @($global_clock) ena && (in == 4'hA) |-> (out == 16h'FBF)
    );

    // When enabled, bit 11 is active low for input 1011.
    check_enabled_bit11_map: assert property (
        @($global_clock) ena && (in == 4'hB) |-> (out == 16h'F7F)
    );

    // When enabled, bit 12 is active low for input 1100.
    check_enabled_bit12_map: assert property (
        @($global_clock) ena && (in == 4'hC) |-> (out == 16h'F3F)
    );

    // When enabled, bit 13 is active low for input 1101.
    check_enabled_bit13_map: assert property (
        @($global_clock) ena && (in == 4'hD) |-> (out == 16h'F1F)
    );

    // When enabled, bit 14 is active low for input 1110.
    check_enabled_bit14_map: assert property (
        @($global_clock) ena && (in == 4'hE) |-> (out == 16h'EFF)
    );

    // When enabled, bit 15 is active low for input 1111.
    check_enabled_bit15_map: assert property (
        @($global_clock) ena && (in == 4'hF) |-> (out == 16h'FFF)
    );

endmodule