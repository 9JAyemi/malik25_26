module decoder_4to16_sva (
    input logic        clk,
    input logic [255:0] in,
    input logic [3:0]   sel,
    input logic [15:0]  out
);

    // sel 0000 decodes to bit 0.
    check_sel_0000_decode: assert property (
        @(posedge clk) (sel == 4'b0000) |-> (out == 16'h0001)
    );

    // sel 0001 decodes to bit 1.
    check_sel_0001_decode: assert property (
        @(posedge clk) (sel == 4'b0001) |-> (out == 16'h0002)
    );

    // sel 0010 decodes to bit 2.
    check_sel_0010_decode: assert property (
        @(posedge clk) (sel == 4'b0010) |-> (out == 16'h0004)
    );

    // sel 0011 decodes to bit 3.
    check_sel_0011_decode: assert property (
        @(posedge clk) (sel == 4'b0011) |-> (out == 16'h0008)
    );

    // sel 0100 decodes to bit 4.
    check_sel_0100_decode: assert property (
        @(posedge clk) (sel == 4'b0100) |-> (out == 16'h0010)
    );

    // sel 0101 decodes to bit 5.
    check_sel_0101_decode: assert property (
        @(posedge clk) (sel == 4'b0101) |-> (out == 16'h0020)
    );

    // sel 0110 decodes to bit 6.
    check_sel_0110_decode: assert property (
        @(posedge clk) (sel == 4'b0110) |-> (out == 16'h0040)
    );

    // sel 0111 decodes to bit 7.
    check_sel_0111_decode: assert property (
        @(posedge clk) (sel == 4'b0111) |-> (out == 16'h0080)
    );

    // sel 1000 decodes to bit 8.
    check_sel_1000_decode: assert property (
        @(posedge clk) (sel == 4'b1000) |-> (out == 16'h0100)
    );

    // sel 1001 decodes to bit 9.
    check_sel_1001_decode: assert property (
        @(posedge clk) (sel == 4'b1001) |-> (out == 16'h0200)
    );

    // sel 1010 decodes to bit 10.
    check_sel_1010_decode: assert property (
        @(posedge clk) (sel == 4'b1010) |-> (out == 16'h0400)
    );

    // sel 1011 decodes to bit 11.
    check_sel_1011_decode: assert property (
        @(posedge clk) (sel == 4'b1011) |-> (out == 16'h0800)
    );

    // sel 1100 decodes to bit 12.
    check_sel_1100_decode: assert property (
        @(posedge clk) (sel == 4'b1100) |-> (out == 16'h1000)
    );

    // sel 1101 decodes to bit 13.
    check_sel_1101_decode: assert property (
        @(posedge clk) (sel == 4'b1101) |-> (out == 16'h2000)
    );

    // sel 1110 decodes to bit 14.
    check_sel_1110_decode: assert property (
        @(posedge clk) (sel == 4'b1110) |-> (out == 16'h4000)
    );

    // sel 1111 decodes to bit 15.
    check_sel_1111_decode: assert property (
        @(posedge clk) (sel == 4'b1111) |-> (out == 16'h8000)
    );

    // Any non-matching select value drives zero.
    check_default_decode_zero: assert property (
        @(posedge clk) (sel != 4'b0000 && sel != 4'b0001 && sel != 4'b0010 && sel != 4'b0011 &&
                        sel != 4'b0100 && sel != 4'b0101 && sel != 4'b0110 && sel != 4'b0111 &&
                        sel != 4'b1000 && sel != 4'b1001 && sel != 4'b1010 && sel != 4'b1011 &&
                        sel != 4'b1100 && sel != 4'b1101 && sel != 4'b1110 && sel != 4'b1111)
        |-> (out == 16'h0000)
    );

endmodule