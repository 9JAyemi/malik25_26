module decoder_2to4_sva (
    input logic [1:0] in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // Input 00 decodes to out0 high and the others low.
    check_decode_00: assert property (
        @($global_clock) (in == 2'b00) |-> (out0 && !out1 && !out2 && !out3)
    );

    // Input 01 decodes to out1 high and the others low.
    check_decode_01: assert property (
        @($global_clock) (in == 2'b01) |-> (!out0 && out1 && !out2 && !out3)
    );

    // Input 10 decodes to out2 high and the others low.
    check_decode_10: assert property (
        @($global_clock) (in == 2'b10) |-> (!out0 && !out1 && out2 && !out3)
    );

    // Input 11 decodes to out3 high and the others low.
    check_decode_11: assert property (
        @($global_clock) (in == 2'b11) |-> (!out0 && !out1 && !out2 && out3)
    );

    // Exactly one output is high for all input values.
    check_onehot_output: assert property (
        @($global_clock) $onehot({out0, out1, out2, out3})
    );

endmodule