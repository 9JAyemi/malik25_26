module decoder_2to4_sva (
    input logic clk,
    input logic [1:0] in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // 00 decodes to out0 high and the others low.
    check_decode_00: assert property (
        @(posedge clk) (in == 2'b00) |-> (out0 == 1'b1 && out1 == 1'b0 && out2 == 1'b0 && out3 == 1'b0)
    );

    // 01 decodes to out1 high and the others low.
    check_decode_01: assert property (
        @(posedge clk) (in == 2'b01) |-> (out0 == 1'b0 && out1 == 1'b1 && out2 == 1'b0 && out3 == 1'b0)
    );

    // 10 decodes to out2 high and the others low.
    check_decode_10: assert property (
        @(posedge clk) (in == 2'b10) |-> (out0 == 1'b0 && out1 == 1'b0 && out2 == 1'b1 && out3 == 1'b0)
    );

    // 11 decodes to out3 high and the others low.
    check_decode_11: assert property (
        @(posedge clk) (in == 2'b11) |-> (out0 == 1'b0 && out1 == 1'b0 && out2 == 1'b0 && out3 == 1'b1)
    );

    // The outputs are always one-hot or all low.
    check_output_onehot0: assert property (
        @(posedge clk) $onehot0({out3, out2, out1, out0})
    );

    // out0 is high only for input 00.
    check_out0_only_for_00: assert property (
        @(posedge clk) out0 |-> (in == 2'b00)
    );

    // out1 is high only for input 01.
    check_out1_only_for_01: assert property (
        @(posedge clk) out1 |-> (in == 2'b01)
    );

    // out2 is high only for input 10.
    check_out2_only_for_10: assert property (
        @(posedge clk) out2 |-> (in == 2'b10)
    );

    // out3 is high only for input 11.
    check_out3_only_for_11: assert property (
        @(posedge clk) out3 |-> (in == 2'b11)
    );

endmodule