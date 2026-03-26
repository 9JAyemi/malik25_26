module decoder_2to4_sva (
    input logic [1:0] in,
    input logic [3:0] out
);

    // Input 00 decodes to bit 0 high.
    check_decode_input_00: assert property (
        @($global_clock) (in == 2'b00) |-> (out == 4'b0001)
    );

    // Input 01 decodes to bit 1 high.
    check_decode_input_01: assert property (
        @($global_clock) (in == 2'b01) |-> (out == 4'b0010)
    );

    // Input 10 decodes to bit 2 high.
    check_decode_input_10: assert property (
        @($global_clock) (in == 2'b10) |-> (out == 4'b0100)
    );

    // Input 11 decodes to bit 3 high.
    check_decode_input_11: assert property (
        @($global_clock) (in == 2'b11) |-> (out == 4'b1000)
    );

    // The decoder output is always one-hot.
    check_output_onehot: assert property (
        @($global_clock) $onehot(out)
    );

endmodule