module decoder_4to16_sva (
    input logic [3:0]  in,
    input logic        ena,
    input logic [15:0] out
);

    // Output is always either all ones or exactly one active low bit.
    check_out_shape: assert property (
        @($global_clock) disable iff (1'b0)
        (out == 16'hFFFF) || (out == {15'b0, ~out[0]})
    );

    // Enabled inputs drive exactly one active low bit.
    check_enabled_onehot0: assert property (
        @($global_clock) disable iff (1'b0)
        ena |-> (out == {15'b0, ~out[0]})
    );

    // Disabled inputs drive all ones.
    check_disabled_allones: assert property (
        @($global_clock) disable iff (1'b0)
        !ena |-> (out == 16'hFFFF)
    );

    // Input 0000 selects bit 0 when enabled.
    check_decode_0000: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0000)) |-> (out == 16'hFFFE)
    );

    // Input 0001 selects bit 1 when enabled.
    check_decode_0001: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0001)) |-> (out == 16'hFFFD)
    );

    // Input 0010 selects bit 2 when enabled.
    check_decode_0010: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0010)) |-> (out == 16'hFFFB)
    );

    // Input 0011 selects bit 3 when enabled.
    check_decode_0011: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0011)) |-> (out == 16'hFFF7)
    );

    // Input 0100 selects bit 4 when enabled.
    check_decode_0100: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0100)) |-> (out == 16'hFFEF)
    );

    // Input 0101 selects bit 5 when enabled.
    check_decode_0101: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0101)) |-> (out == 16'hFFDF)
    );

    // Input 0110 selects bit 6 when enabled.
    check_decode_0110: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0110)) |-> (out == 16'hFFBF)
    );

    // Input 0111 selects bit 7 when enabled.
    check_decode_0111: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b0111)) |-> (out == 16'hFF7F)
    );

    // Input 1000 selects bit 8 when enabled.
    check_decode_1000: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1000)) |-> (out == 16'hFEFF)
    );

    // Input 1001 selects bit 9 when enabled.
    check_decode_1001: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1001)) |-> (out == 16'hFDFF)
    );

    // Input 1010 selects bit 10 when enabled.
    check_decode_1010: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1010)) |-> (out == 16'hFBFF)
    );

    // Input 1011 selects bit 11 when enabled.
    check_decode_1011: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1011)) |-> (out == 16'hF7FF)
    );

    // Input 1100 selects bit 12 when enabled.
    check_decode_1100: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1100)) |-> (out == 16h'EFFF)
    );

    // Input 1101 selects bit 13 when enabled.
    check_decode_1101: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1101)) |-> (out == 16h'DFFF)
    );

    // Input 1110 selects bit 14 when enabled.
    check_decode_1110: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1110)) |-> (out == 16h'BFFF)
    );

    // Input 1111 selects bit 15 when enabled.
    check_decode_1111: assert property (
        @($global_clock) disable iff (1'b0)
        (ena && (in == 4'b1111)) |-> (out == 16h'7FFF)
    );

endmodule