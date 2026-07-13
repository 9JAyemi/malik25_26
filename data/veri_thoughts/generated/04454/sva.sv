module decoder_2to4_sva(
    input logic A,
    input logic B,
    input logic enable,
    input logic [3:0] out
);

    // When disabled, the output is zero.
    check_disabled_zero: assert property (
        @($global_clock) (!enable) |-> (out == 4'b0000)
    );

    // Enabled input 00 decodes to 0000.
    check_decode_00: assert property (
        @($global_clock) (enable && !A && !B) |-> (out == 4'b0000)
    );

    // Enabled input 01 decodes to 0100.
    check_decode_01: assert property (
        @($global_clock) (enable && !A && B) |-> (out == 4'b0100)
    );

    // Enabled input 10 decodes to 0110.
    check_decode_10: assert property (
        @($global_clock) (enable && A && !B) |-> (out == 4'b0110)
    );

    // Enabled input 11 decodes to 0111.
    check_decode_11: assert property (
        @($global_clock) (enable && A && B) |-> (out == 4'b0111)
    );

    // The MSB is always driven low.
    check_msb_always_zero: assert property (
        @($global_clock) (out[3] == 1'b0)
    );

endmodule