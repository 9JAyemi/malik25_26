module binary_to_gray_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [2:0] out
);

    // 000 maps to 000.
    check_map_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 3'b000)
    );

    // 001 maps to 001.
    check_map_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 3'b001)
    );

    // 010 maps to 011.
    check_map_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 3'b011)
    );

    // 011 maps to 010.
    check_map_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 3'b010)
    );

    // 100 maps to 110.
    check_map_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 3'b110)
    );

    // 101 maps to 111.
    check_map_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 3'b111)
    );

    // 110 maps to 101.
    check_map_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 3'b101)
    );

    // 111 maps to 100.
    check_map_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 3'b100)
    );

    // Output matches the 3-bit binary-to-Gray formula.
    check_gray_formula: assert property (
        @(posedge clk) out == {in[2], (in[2] ^ in[1]), (in[1] ^ in[0])}
    );

endmodule