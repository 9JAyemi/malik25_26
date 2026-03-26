module four_bit_converter_sva(
    input logic clk,
    input logic [2:0] in,
    input logic [3:0] out
);

    // 000 converts to 0000.
    check_map_000_to_0000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 4'b0000)
    );

    // 001 and 101 convert to 0001.
    check_map_001_101_to_0001: assert property (
        @(posedge clk) ((in == 3'b001) || (in == 3'b101)) |-> (out == 4'b0001)
    );

    // 010 and 110 convert to 0010.
    check_map_010_110_to_0010: assert property (
        @(posedge clk) ((in == 3'b010) || (in == 3'b110)) |-> (out == 4'b0010)
    );

    // 011 and 111 convert to 0100.
    check_map_011_111_to_0100: assert property (
        @(posedge clk) ((in == 3'b011) || (in == 3'b111)) |-> (out == 4'b0100)
    );

    // 100 converts to 1000.
    check_map_100_to_1000: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 4'b1000)
    );

    // 0000 can only come from 000.
    check_rev_0000_from_000: assert property (
        @(posedge clk) (out == 4'b0000) |-> (in == 3'b000)
    );

    // 0001 can only come from 001 or 101.
    check_rev_0001_from_001_101: assert property (
        @(posedge clk) (out == 4'b0001) |-> ((in == 3'b001) || (in == 3'b101))
    );

    // 0010 can only come from 010 or 110.
    check_rev_0010_from_010_110: assert property (
        @(posedge clk) (out == 4'b0010) |-> ((in == 3'b010) || (in == 3'b110))
    );

    // 0100 can only come from 011 or 111.
    check_rev_0100_from_011_111: assert property (
        @(posedge clk) (out == 4'b0100) |-> ((in == 3'b011) || (in == 3'b111))
    );

    // 1000 can only come from 100.
    check_rev_1000_from_100: assert property (
        @(posedge clk) (out == 4'b1000) |-> (in == 3'b100)
    );

endmodule