module priority_encoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);
    // 0000 maps to 00 (default)
    map_0000_to_00: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 2'b00)
    );

    // 0001 maps to 01
    map_0001_to_01: assert property (
        @(posedge clk) (in == 4'b0001) |-> (out == 2'b01)
    );

    // 0010 maps to 10
    map_0010_to_10: assert property (
        @(posedge clk) (in == 4'b0010) |-> (out == 2'b10)
    );

    // 0011 maps to 10
    map_0011_to_10: assert property (
        @(posedge clk) (in == 4'b0011) |-> (out == 2'b10)
    );

    // 0100 maps to 11
    map_0100_to_11: assert property (
        @(posedge clk) (in == 4'b0100) |-> (out == 2'b11)
    );

    // 0101 maps to 11
    map_0101_to_11: assert property (
        @(posedge clk) (in == 4'b0101) |-> (out == 2'b11)
    );

    // 0110 maps to 10
    map_0110_to_10: assert property (
        @(posedge clk) (in == 4'b0110) |-> (out == 2'b10)
    );

    // 0111 maps to 10
    map_0111_to_10: assert property (
        @(posedge clk) (in == 4'b0111) |-> (out == 2'b10)
    );

    // 1000 maps to 00
    map_1000_to_00: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 2'b00)
    );

    // 1001 maps to 00 (default)
    map_1001_to_00: assert property (
        @(posedge clk) (in == 4'b1001) |-> (out == 2'b00)
    );

    // 1010 maps to 10
    map_1010_to_10: assert property (
        @(posedge clk) (in == 4'b1010) |-> (out == 2'b10)
    );

    // 1011 maps to 11
    map_1011_to_11: assert property (
        @(posedge clk) (in == 4'b1011) |-> (out == 2'b11)
    );

    // 1100 maps to 10
    map_1100_to_10: assert property (
        @(posedge clk) (in == 4'b1100) |-> (out == 2'b10)
    );

    // 1101 maps to 11
    map_1101_to_11: assert property (
        @(posedge clk) (in == 4'b1101) |-> (out == 2'b11)
    );

    // 1110 maps to 00 (default)
    map_1110_to_00: assert property (
        @(posedge clk) (in == 4'b1110) |-> (out == 2'b00)
    );

    // 1111 maps to 10
    map_1111_to_10: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 2'b10)
    );
endmodule