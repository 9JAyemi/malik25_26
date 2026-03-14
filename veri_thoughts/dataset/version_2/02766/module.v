
module priority_encoder (
    input [7:0] in,
    output [2:0] pos );

    assign pos = in[7] ? 7 :
                   in[6] ? 6 :
                   in[5] ? 5 :
                   in[4] ? 4 :
                   in[3] ? 3 :
                   in[2] ? 2 :
                   in[1] ? 1 :
                   in[0] ? 0 : 0;

endmodule
module top_module (
    input [7:0] in,
    output [2:0] pos );

    priority_encoder pe(in, pos);

endmodule