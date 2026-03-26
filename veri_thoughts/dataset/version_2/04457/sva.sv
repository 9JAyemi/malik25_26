module decoder_3to8_sva (
    input logic [2:0] in,
    input logic [7:0] out
);

    // No explicit clock or reset in RTL; sample on Jasper global clock.

    // Output matches the one-hot decode of the input value.
    check_decode_matches_input: assert property (
        @($global_clock) out == (8'b00000001 << in)
    );

    // out[0] is high only for input 000.
    check_out0_decode: assert property (
        @($global_clock) out[0] == (in == 3'b000)
    );

    // out[1] is high only for input 001.
    check_out1_decode: assert property (
        @($global_clock) out[1] == (in == 3'b001)
    );

    // out[2] is high only for input 010.
    check_out2_decode: assert property (
        @($global_clock) out[2] == (in == 3'b010)
    );

    // out[3] is high only for input 011.
    check_out3_decode: assert property (
        @($global_clock) out[3] == (in == 3'b011)
    );

    // out[4] is high only for input 100.
    check_out4_decode: assert property (
        @($global_clock) out[4] == (in == 3'b100)
    );

    // out[5] is high only for input 101.
    check_out5_decode: assert property (
        @($global_clock) out[5] == (in == 3'b101)
    );

    // out[6] is high only for input 110.
    check_out6_decode: assert property (
        @($global_clock) out[6] == (in == 3'b110)
    );

    // out[7] is high only for input 111.
    check_out7_decode: assert property (
        @($global_clock) out[7] == (in == 3'b111)
    );

    // The decoder output always has exactly one bit set.
    check_output_onehot: assert property (
        @($global_clock) $onehot(out)
    );

endmodule