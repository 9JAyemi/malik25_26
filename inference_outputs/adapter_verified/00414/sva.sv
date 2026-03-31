module decoder_4to16_sva (
    input logic        clk,
    input logic [255:0]in,
    input logic [3:0]  sel,
    input logic [15:0] out
);

// sel=0000 drives only bit 0 high.
    check_sel_0000: assert property (
        @(posedge clk) (sel == 4'b0000) |-> (out == 16'h0001)
    );

// sel=0001 drives only bit 1 high.
    check_sel_0001: assert property (
        @(posedge clk) (sel == 4'b0001) |-> (out == 16'h0002)
    );

// sel=0010 drives only bit 2 high.
    check_sel_0010: assert property (
        @(posedge clk) (sel == 4'b0010) |-> (out == 16'h0004)
    );

// sel=0011 drives only bit 3 high.
    check_sel_0011: assert property (
        @(posedge clk) (sel == 4'b0011) |-> (out == 16'h0008)
    );

// sel=0100 drives only bit 4 high.
    check_sel_0100: assert property (
        @(posedge clk) (sel == 4'b0100) |-> (out == 16'h0010)
    );

// sel=0101 drives only bit 5 high.
    check_sel_0101: assert property (
        @(posedge clk) (sel == 4'b0101) |-> (out == 16'h0020)
    );

// sel=0110 drives only bit 6 high.
    check_sel_0110: assert property (
        @(posedge clk) (sel == 4'b0110) |-> (out == 16'h0040)
    );

// sel=0111 drives only bit 7 high.
    check_sel_0111: assert property (
        @(posedge clk) (sel == 4'b0111) |-> (out == 16'h0080)
    );

// sel=1000 drives only bit 8 high.
    check_sel_1000: assert property (
        @(posedge clk) (sel == 4'b1000) |-> (out == 16'h0100)
    );

// sel=1001 drives only bit 9 high.
    check_sel_1001: assert property (
        @(posedge clk) (sel == 4'b1001) |-> (out == 16'h0200)
    );

// sel=1010 drives only bit 10 high.
    check_sel_1010: assert property (
        @(posedge clk) (sel == 4'b1010) |-> (out == 16'h0400)
    );

// sel=1011 drives only bit 11 high.
    check_sel_1011: assert property (
        @(posedge clk) (sel == 4'b1011) |-> (out == 16'h0800)
    );

// sel=1100 drives only bit 12 high.
    check_sel_1100: assert property (
        @(posedge clk) (sel == 4'b1100) |-> (out == 16'h1000)
    );

// sel=1101 drives only bit 13 high.
    check_sel_1101: assert property (
        @(posedge clk) (sel == 4'b1101) |-> (out == 16'h2000)
    );

// sel=1110 drives only bit 14 high.
    check_sel_1110: assert property (
        @(posedge clk) (sel == 4'b1110) |-> (out == 16'h4000)
    );

// sel=1111 drives only bit 15 high.
    check_sel_1111: assert property (
        @(posedge clk) (sel == 4'b1111) |-> (out == 16'h8000)
    );

// Any non-listed sel value drives zero.
    check_default_zero: assert property (
        @(posedge clk) (sel > 4'hF) |-> (out == 16'h0000)
    );

endmodule
