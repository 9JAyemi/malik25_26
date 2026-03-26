module decoder_2to4_priority_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic [3:0] Y
);

    // The upper two output bits are always cleared.
    check_upper_bits_zero: assert property (
        @(posedge clk) Y[3:2] == 2'b00
    );

    // A=0 and B=0 drives Y to 0000.
    check_decode_00: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0) |-> (Y == 4'b0000)
    );

    // A=1 and B=0 drives Y to 0001.
    check_decode_10: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b0) |-> (Y == 4'b0001)
    );

    // A=0 and B=1 drives Y to 0010.
    check_decode_01: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b1) |-> (Y == 4'b0010)
    );

    // A=1 and B=1 drives Y to 0011.
    check_decode_11: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1) |-> (Y == 4'b0011)
    );

endmodule