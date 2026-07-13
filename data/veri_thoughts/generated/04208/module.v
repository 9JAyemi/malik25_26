module decoder_3to8 (
    Y7,
    Y6,
    Y5,
    Y4,
    Y3,
    Y2,
    Y1,
    Y0,
    A2,
    A1,
    A0
);

    // Module ports
    output Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0;
    input  A2, A1, A0;

    // 3-to-8 decoder logic
    assign Y7 = (A2 & A1 & A0) ? 1'b1 : 1'b0;
    assign Y6 = (A2 & A1 & ~A0) ? 1'b1 : 1'b0;
    assign Y5 = (A2 & ~A1 & A0) ? 1'b1 : 1'b0;
    assign Y4 = (A2 & ~A1 & ~A0) ? 1'b1 : 1'b0;
    assign Y3 = (~A2 & A1 & A0) ? 1'b1 : 1'b0;
    assign Y2 = (~A2 & A1 & ~A0) ? 1'b1 : 1'b0;
    assign Y1 = (~A2 & ~A1 & A0) ? 1'b1 : 1'b0;
    assign Y0 = (~A2 & ~A1 & ~A0) ? 1'b1 : 1'b0;

endmodule