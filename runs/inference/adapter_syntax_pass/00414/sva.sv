module decoder_4to16_sva (
    input logic [255:0] in,
    input logic [3:0] sel,
    input logic [15:0] out
);

    // sel=0000 decodes to bit 0.
    check_sel_0000_decode: assert property (
        @($global_clock) (sel == 4'h0) |-> (out == 16'h0001)
    );

    // sel=0001 decodes to bit 1.
    check_sel_0001_decode: assert property (
        @($global_clock) (sel == 4'h1) |-> (out == 16'h0002)
    );

    // sel=0010 decodes to bit 2.
    check_sel_0010_decode: assert property (
        @($global_clock) (sel == 4'h2) |-> (out == 16'h0004)
    );

    // sel=0011 decodes to bit 3.
    check_sel_0011_decode: assert property (
        @($global_clock) (sel == 4'h3) |-> (out == 16'h0008)
    );

    // sel=0100 decodes to bit 4.
    check_sel_0100_decode: assert property (
        @($global_clock) (sel == 4'h4) |-> (out == 16'h0010)
    );

    // sel=0101 decodes to bit 5.
    check_sel_0101_decode: assert property (
        @($global_clock) (sel == 4'h5) |-> (out == 16'h0020)
    );

    // sel=0110 decodes to bit 6.
    check_sel_0110_decode: assert property (
        @($global_clock) (sel == 4'h6) |-> (out == 16'h0040)
    );

    // sel=0111 decodes to bit 7.
    check_sel_0111_decode: assert property (
        @($global_clock) (sel == 4'h7) |-> (out == 16'h0080)
    );

    // sel=1000 decodes to bit 8.
    check_sel_1000_decode: assert property (
        @($global_clock) (sel == 4'h8) |-> (out == 16'h0100)
    );

    // sel=1001 decodes to bit 9.
    check_sel_1001_decode: assert property (
        @($global_clock) (sel == 4'h9) |-> (out == 16'h0200)
    );

    // sel=1010 decodes to bit 10.
    check_sel_1010_decode: assert property (
        @($global_clock) (sel == 4'hA) |-> (out == 16'h0400)
    );

    // sel=1011 decodes to bit 11.
    check_sel_1011_decode: assert property (
        @($global_clock) (sel == 4'hB) |-> (out == 16'h0800)
    );

    // sel=1100 decodes to bit 12.
    check_sel_1100_decode: assert property (
        @($global_clock) (sel == 4'hC) |-> (out == 16'h1000)
    );

    // sel=1101 decodes to bit 13.
    check_sel_1101_decode: assert property (
        @($global_clock) (sel == 4'hD) |-> (out == 16'h2000)
    );

    // sel=1110 decodes to bit 14.
    check_sel_1110_decode: assert property (
        @($global_clock) (sel == 4'hE) |-> (out == 16'h4000)
    );

    // sel=1111 decodes to bit 15.
    check_sel_1111_decode: assert property (
        @($global_clock) (sel == 4'hF) |-> (out == 16'h8000)
    );

    // Any non-binary select value drives zero.
    check_default_decode_zero: assert property (
        @($global_clock) (sel[1:0] != 2'b00) |-> (out == 16'h0000)
    );

endmodule