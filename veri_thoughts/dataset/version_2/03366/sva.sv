module decoder_3to8_sva (
    input logic       clk,
    input logic [2:0] abc,
    input logic [7:0] d
);

    // abc 000 decodes to bit 0 set.
    check_decode_000: assert property (
        @(posedge clk) (abc == 3'b000) |-> (d == 8'b00000001)
    );

    // abc 001 decodes to bit 1 set.
    check_decode_001: assert property (
        @(posedge clk) (abc == 3'b001) |-> (d == 8'b00000010)
    );

    // abc 010 decodes to bit 2 set.
    check_decode_010: assert property (
        @(posedge clk) (abc == 3'b010) |-> (d == 8'b00000100)
    );

    // abc 011 decodes to bit 3 set.
    check_decode_011: assert property (
        @(posedge clk) (abc == 3'b011) |-> (d == 8'b00001000)
    );

    // abc 100 decodes to bit 4 set.
    check_decode_100: assert property (
        @(posedge clk) (abc == 3'b100) |-> (d == 8'b00010000)
    );

    // abc 101 decodes to bit 5 set.
    check_decode_101: assert property (
        @(posedge clk) (abc == 3'b101) |-> (d == 8'b00100000)
    );

    // abc 110 decodes to bit 6 set.
    check_decode_110: assert property (
        @(posedge clk) (abc == 3'b110) |-> (d == 8'b01000000)
    );

    // abc 111 decodes to bit 7 set.
    check_decode_111: assert property (
        @(posedge clk) (abc == 3'b111) |-> (d == 8'b10000000)
    );

endmodule