
module priority_encoder (
    input [7:0] in,
    output [2:0] pos );

    wire [2:0] pos_int;

    assign pos_int = in[2:0];

    assign pos = ~pos_int;

endmodule
module top_module (
    input [7:0] in,
    output [2:0] pos );

    priority_encoder pe(in, pos);

endmodule