module decoder_2to4_sva (
    input logic clk,
    input logic [1:0] in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // Input 00 selects only out0.
    check_decode_00: assert property (
        @(posedge clk) (in == 2'b00) |-> ({out3, out2, out1, out0} == 4'b0001)
    );

    // Input 01 selects only out1.
    check_decode_01: assert property (
        @(posedge clk) (in == 2'b01) |-> ({out3, out2, out1, out0} == 4'b0010)
    );

    // Input 10 selects only out2.
    check_decode_10: assert property (
        @(posedge clk) (in == 2'b10) |-> ({out3, out2, out1, out0} == 4'b0100)
    );

    // Input 11 selects only out3.
    check_decode_11: assert property (
        @(posedge clk) (in == 2'b11) |-> ({out3, out2, out1, out0} == 4'b1000)
    );

    // For any binary input, exactly one output is asserted.
    check_outputs_onehot: assert property (
        @(posedge clk)
        ((in == 2'b00) || (in == 2'b01) || (in == 2'b10) || (in == 2'b11))
        |-> $onehot({out3, out2, out1, out0})
    );

endmodule