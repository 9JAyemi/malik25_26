
module decoder_3to8 (
    input [2:0] IN,
    output [7:0] OUT
);

    assign OUT[0] = ~IN[2] & ~IN[1] & ~IN[0];
    assign OUT[1] = ~IN[2] & ~IN[1] &  IN[0];
    assign OUT[2] = ~IN[2] &  IN[1] & ~IN[0];
    assign OUT[3] = ~IN[2] &  IN[1] &  IN[0];
    assign OUT[4] =  IN[2] & ~IN[1] & ~IN[0];
    assign OUT[5] =  IN[2] & ~IN[1] &  IN[0];
    assign OUT[6] =  IN[2] &  IN[1] & ~IN[0];
    assign OUT[7] =  IN[2] &  IN[1] &  IN[0];

endmodule