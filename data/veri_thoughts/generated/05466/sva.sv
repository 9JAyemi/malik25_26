module decoder_3to8_sva (
    input logic       clk,
    input logic [2:0] IN,
    input logic [7:0] OUT
);

    // IN=000 decodes to OUT[0].
    check_decode_000: assert property (
        @(posedge clk) (IN == 3'b000) |-> (OUT == 8'b0000_0001)
    );

    // IN=001 decodes to OUT[1].
    check_decode_001: assert property (
        @(posedge clk) (IN == 3'b001) |-> (OUT == 8'b0000_0010)
    );

    // IN=010 decodes to OUT[2].
    check_decode_010: assert property (
        @(posedge clk) (IN == 3'b010) |-> (OUT == 8'b0000_0100)
    );

    // IN=011 decodes to OUT[3].
    check_decode_011: assert property (
        @(posedge clk) (IN == 3'b011) |-> (OUT == 8'b0000_1000)
    );

    // IN=100 decodes to OUT[4].
    check_decode_100: assert property (
        @(posedge clk) (IN == 3'b100) |-> (OUT == 8'b0001_0000)
    );

    // IN=101 decodes to OUT[5].
    check_decode_101: assert property (
        @(posedge clk) (IN == 3'b101) |-> (OUT == 8'b0010_0000)
    );

    // IN=110 decodes to OUT[6].
    check_decode_110: assert property (
        @(posedge clk) (IN == 3'b110) |-> (OUT == 8'b0100_0000)
    );

    // IN=111 decodes to OUT[7].
    check_decode_111: assert property (
        @(posedge clk) (IN == 3'b111) |-> (OUT == 8'b1000_0000)
    );

    // OUT matches a left-shifted one-hot decode of IN.
    check_exact_shift_decode: assert property (
        @(posedge clk) OUT == (8'b0000_0001 << IN)
    );

    // OUT is always exactly one-hot.
    check_onehot_output: assert property (
        @(posedge clk) $onehot(OUT)
    );

endmodule