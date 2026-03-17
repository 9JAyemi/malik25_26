module binary_to_onehot_sva (
    input logic clk,
    input logic [3:0] B,
    input logic [7:0] O
);

    // 0001 maps to output bit 0.
    check_map_0001: assert property (
        @(posedge clk) (B == 4'b0001) |-> (O == 8'b00000001)
    );

    // 0010 maps to output bit 1.
    check_map_0010: assert property (
        @(posedge clk) (B == 4'b0010) |-> (O == 8'b00000010)
    );

    // 0100 maps to output bit 2.
    check_map_0100: assert property (
        @(posedge clk) (B == 4'b0100) |-> (O == 8'b00000100)
    );

    // 1000 maps to output bit 3.
    check_map_1000: assert property (
        @(posedge clk) (B == 4'b1000) |-> (O == 8'b00001000)
    );

    // All other input values drive zero.
    check_default_zero: assert property (
        @(posedge clk)
        ((B != 4'b0001) && (B != 4'b0010) && (B != 4'b0100) && (B != 4'b1000))
        |-> (O == 8'b00000000)
    );

    // The upper four output bits are always zero.
    check_upper_bits_zero: assert property (
        @(posedge clk) (O[7:4] == 4'b0000)
    );

endmodule