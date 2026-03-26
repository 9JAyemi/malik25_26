module binary_decoder_sva (
    input logic clk,
    input logic [3:0] sw,
    input logic [3:0] led
);

    // 0000 maps to 0001.
    check_decode_0000: assert property (
        @(posedge clk) (sw == 4'b0000) |-> (led == 4'b0001)
    );

    // 0001 maps to 0010.
    check_decode_0001: assert property (
        @(posedge clk) (sw == 4'b0001) |-> (led == 4'b0010)
    );

    // 0010 maps to 0011.
    check_decode_0010: assert property (
        @(posedge clk) (sw == 4'b0010) |-> (led == 4'b0011)
    );

    // 0011 maps to 0100.
    check_decode_0011: assert property (
        @(posedge clk) (sw == 4'b0011) |-> (led == 4'b0100)
    );

    // 0100 maps to 0101.
    check_decode_0100: assert property (
        @(posedge clk) (sw == 4'b0100) |-> (led == 4'b0101)
    );

    // 0101 maps to 0110.
    check_decode_0101: assert property (
        @(posedge clk) (sw == 4'b0101) |-> (led == 4'b0110)
    );

    // 0110 maps to 0111.
    check_decode_0110: assert property (
        @(posedge clk) (sw == 4'b0110) |-> (led == 4'b0111)
    );

    // 0111 maps to 1000.
    check_decode_0111: assert property (
        @(posedge clk) (sw == 4'b0111) |-> (led == 4'b1000)
    );

    // 1000 maps to 1001.
    check_decode_1000: assert property (
        @(posedge clk) (sw == 4'b1000) |-> (led == 4'b1001)
    );

    // 1001 maps to 1010.
    check_decode_1001: assert property (
        @(posedge clk) (sw == 4'b1001) |-> (led == 4'b1010)
    );

    // 1010 maps to 1011.
    check_decode_1010: assert property (
        @(posedge clk) (sw == 4'b1010) |-> (led == 4'b1011)
    );

    // 1011 maps to 1100.
    check_decode_1011: assert property (
        @(posedge clk) (sw == 4'b1011) |-> (led == 4'b1100)
    );

    // 1100 maps to 1101.
    check_decode_1100: assert property (
        @(posedge clk) (sw == 4'b1100) |-> (led == 4'b1101)
    );

    // 1101 maps to 1110.
    check_decode_1101: assert property (
        @(posedge clk) (sw == 4'b1101) |-> (led == 4'b1110)
    );

    // 1110 maps to 1111.
    check_decode_1110: assert property (
        @(posedge clk) (sw == 4'b1110) |-> (led == 4'b1111)
    );

    // 1111 wraps to 0000.
    check_decode_1111: assert property (
        @(posedge clk) (sw == 4'b1111) |-> (led == 4'b0000)
    );

endmodule