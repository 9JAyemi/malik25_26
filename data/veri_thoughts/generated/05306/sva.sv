module decoder_4to16_sva (
    input logic [3:0]  in,
    input logic [15:0] out
);

    // No explicit clock or reset exists; sample on the formal global clock.

    // out[0] matches the 0000 decode term.
    check_out0_decode: assert property (
        @($global_clock) out[0] == (~(in[3] | in[2] | in[1] | in[0]))
    );

    // out[1] matches the 0001 decode term.
    check_out1_decode: assert property (
        @($global_clock) out[1] == (~(in[3] | in[2] | in[1] | ~in[0]))
    );

    // out[2] matches the 0010 decode term.
    check_out2_decode: assert property (
        @($global_clock) out[2] == (~(in[3] | in[2] | ~in[1] | in[0]))
    );

    // out[3] matches the 0011 decode term.
    check_out3_decode: assert property (
        @($global_clock) out[3] == (~(in[3] | in[2] | ~in[1] | ~in[0]))
    );

    // out[4] matches the 0100 decode term.
    check_out4_decode: assert property (
        @($global_clock) out[4] == (~(in[3] | ~in[2] | in[1] | in[0]))
    );

    // out[5] matches the 0101 decode term.
    check_out5_decode: assert property (
        @($global_clock) out[5] == (~(in[3] | ~in[2] | in[1] | ~in[0]))
    );

    // out[6] matches the 0110 decode term.
    check_out6_decode: assert property (
        @($global_clock) out[6] == (~(in[3] | ~in[2] | ~in[1] | in[0]))
    );

    // out[7] matches the 0111 decode term.
    check_out7_decode: assert property (
        @($global_clock) out[7] == (~(in[3] | ~in[2] | ~in[1] | ~in[0]))
    );

    // out[8] matches the 1000 decode term.
    check_out8_decode: assert property (
        @($global_clock) out[8] == (~(~in[3] | in[2] | in[1] | in[0]))
    );

    // out[9] matches the 1001 decode term.
    check_out9_decode: assert property (
        @($global_clock) out[9] == (~(~in[3] | in[2] | in[1] | ~in[0]))
    );

    // out[10] matches the 1010 decode term.
    check_out10_decode: assert property (
        @($global_clock) out[10] == (~(~in[3] | in[2] | ~in[1] | in[0]))
    );

    // out[11] matches the 1011 decode term.
    check_out11_decode: assert property (
        @($global_clock) out[11] == (~(~in[3] | in[2] | ~in[1] | ~in[0]))
    );

    // out[12] matches the 1100 decode term.
    check_out12_decode: assert property (
        @($global_clock) out[12] == (~(~in[3] | ~in[2] | in[1] | in[0]))
    );

    // out[13] matches the 1101 decode term.
    check_out13_decode: assert property (
        @($global_clock) out[13] == (~(~in[3] | ~in[2] | in[1] | ~in[0]))
    );

    // out[14] matches the 1110 decode term.
    check_out14_decode: assert property (
        @($global_clock) out[14] == (~(~in[3] | ~in[2] | ~in[1] | in[0]))
    );

    // out[15] matches the 1111 decode term.
    check_out15_decode: assert property (
        @($global_clock) out[15] == (~(~in[3] | ~in[2] | ~in[1] | ~in[0]))
    );

    // The decoder output is always exactly one-hot.
    check_out_onehot: assert property (
        @($global_clock) $onehot(out)
    );

endmodule