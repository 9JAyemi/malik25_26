module gray_code_sva (
    input logic [3:0] in,
    input logic [5:0] out
);

    // out[0] mirrors in[0].
    check_out0_mirrors_in0: assert property (
        @($global_clock) out[0] == in[0]
    );

    // out[1] is the XOR of in[0] and in[1].
    check_out1_is_xor_in0_in1: assert property (
        @($global_clock) out[1] == (in[0] ^ in[1])
    );

    // out[2] is the XOR of in[1] and in[2].
    check_out2_is_xor_in1_in2: assert property (
        @($global_clock) out[2] == (in[1] ^ in[2])
    );

    // out[3] is the XOR of in[2] and in[3].
    check_out3_is_xor_in2_in3: assert property (
        @($global_clock) out[3] == (in[2] ^ in[3])
    );

    // out[4] simplifies to in[2].
    check_out4_equals_in2: assert property (
        @($global_clock) out[4] == in[2]
    );

    // out[5] is the XOR of in[1], in[2], and in[3].
    check_out5_is_xor_in1_in2_in3: assert property (
        @($global_clock) out[5] == (in[1] ^ in[2] ^ in[3])
    );

    // The full output vector matches the implemented combinational mapping.
    check_full_output_mapping: assert property (
        @($global_clock)
        out == { (in[1] ^ in[2] ^ in[3]),
                 in[2],
                 (in[2] ^ in[3]),
                 (in[1] ^ in[2]),
                 (in[0] ^ in[1]),
                 in[0] }
    );

endmodule