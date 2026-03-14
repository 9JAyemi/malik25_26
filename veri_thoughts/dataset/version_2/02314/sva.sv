module four_to_two_sva (
    input  logic        clk,   // verification clock (DUT has no clock/reset)
    input  logic [3:0]  in,
    input  logic [1:0]  out
);
    // LSB is odd parity of input bits.
    check_lsb_parity: assert property (
        @(posedge clk) out[0] == (^in)
    );

    // MSB is 1 iff exactly 2 or 3 ones (not all four).
    check_msb_two_or_three: assert property (
        @(posedge clk)
            out[1] == ( ((in[0]&in[1]) | (in[0]&in[2]) | (in[0]&in[3]) | (in[1]&in[2]) | (in[1]&in[3]) | (in[2]&in[3])) & ~(&in) )
    );

    // 0000 maps to 00.
    check_map_0000: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 2'b00)
    );

    // 0001 maps to 01.
    check_map_0001: assert property (
        @(posedge clk) (in == 4'b0001) |-> (out == 2'b01)
    );

    // 0010 maps to 01.
    check_map_0010: assert property (
        @(posedge clk) (in == 4'b0010) |-> (out == 2'b01)
    );

    // 0011 maps to 10.
    check_map_0011: assert property (
        @(posedge clk) (in == 4'b0011) |-> (out == 2'b10)
    );

    // 0100 maps to 01.
    check_map_0100: assert property (
        @(posedge clk) (in == 4'b0100) |-> (out == 2'b01)
    );

    // 0101 maps to 10.
    check_map_0101: assert property (
        @(posedge clk) (in == 4'b0101) |-> (out == 2'b10)
    );

    // 0110 maps to 10.
    check_map_0110: assert property (
        @(posedge clk) (in == 4'b0110) |-> (out == 2'b10)
    );

    // 0111 maps to 11.
    check_map_0111: assert property (
        @(posedge clk) (in == 4'b0111) |-> (out == 2'b11)
    );

    // 1000 maps to 01.
    check_map_1000: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 2'b01)
    );

    // 1001 maps to 10.
    check_map_1001: assert property (
        @(posedge clk) (in == 4'b1001) |-> (out == 2'b10)
    );

    // 1010 maps to 10.
    check_map_1010: assert property (
        @(posedge clk) (in == 4'b1010) |-> (out == 2'b10)
    );

    // 1011 maps to 11.
    check_map_1011: assert property (
        @(posedge clk) (in == 4'b1011) |-> (out == 2'b11)
    );

    // 1100 maps to 10.
    check_map_1100: assert property (
        @(posedge clk) (in == 4'b1100) |-> (out == 2'b10)
    );

    // 1101 maps to 11.
    check_map_1101: assert property (
        @(posedge clk) (in == 4'b1101) |-> (out == 2'b11)
    );

    // 1110 maps to 11.
    check_map_1110: assert property (
        @(posedge clk) (in == 4'b1110) |-> (out == 2'b11)
    );

    // 1111 maps to 00.
    check_map_1111: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 2'b00)
    );
endmodule