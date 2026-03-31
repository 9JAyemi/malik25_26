module decoder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic [15:0] O
);

    // O must always be one-hot or zero.
    check_output_onehot0: assert property (
        @(posedge clk) $onehot0(O)
    );

    // When A and B are both low, only O0 is high.
    check_decode_00: assert property (
        @(posedge clk) ({A, B} == 2'b00) |-> (O == 16'h0001)
    );

    // When A is low and B is high, only O1 is high.
    check_decode_01: assert property (
        @(posedge clk) ({A, B} == 2'b01) |-> (O == 16'h0002)
    );

    // When A is high and B is low, only O2 is high.
    check_decode_10: assert property (
        @(posedge clk) ({A, B} == 2'b10) |-> (O == 16'h0004)
    );

    // When A and B are both high, only O3 is high.
    check_decode_11: assert property (
        @(posedge clk) ({A, B} == 2'b11) |-> (O == 16'h0008)
    );

endmodule