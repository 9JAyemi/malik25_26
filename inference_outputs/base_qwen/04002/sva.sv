module decoder_sva (
    input logic A,
    input logic B,
    input logic CLK,
    input logic RESETn,
    output logic [15:0] O
);
    // Decoder output should be 0 when A and B are both 0
    decoder_0: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 1 when A is 0 and B is 1
    decoder_1: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b1) |-> (O == 16'b0000000000000001)
    );

    // Decoder output should be 2 when A is 1 and B is 0
    decoder_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1 && B == 1'b0) |-> (O == 16'b0000000000000010)
    );

    // Decoder output should be 4 when A and B are both 1
    decoder_3: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1 && B == 1'b1) |-> (O == 16'b0000000000000100)
    );

    // Decoder output should be 8 when A and B are both 1
    decoder_4: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1 && B == 1'b1) |-> (O == 16'b0000000000001000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_5: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_6: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_7: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_8: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_9: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_10: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_12: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_13: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_14: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );

    // Decoder output should be 0 when A and B are both 0
    decoder_15: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0 && B == 1'b0) |-> (O == 16'b0000000000000000)
    );
endmodule