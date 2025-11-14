
module priority_encoder (
    input [7:0] in,
    output [3:0] pos
);

// Assign the position of the highest priority input to 'pos'
assign pos = (in[0] ? 3'b000 :
            in[1] ? 3'b001 :
            in[2] ? 3'b010 :
            in[3] ? 3'b011 :
            in[4] ? 3'b100 :
            in[5] ? 3'b101 :
            in[6] ? 3'b110 : 3'b111);

endmodule

module subtractor (
    input [3:0] in,
    output [3:0] out
);

// Subtract 4'b0101 from the input
assign out = in - 4'b0101;

endmodule

module top_module (
    input [7:0] in,
    output [3:0] out
);

wire [3:0] pos;
priority_encoder pe(
    .in(in),
    .pos(pos)
);

subtractor sub(
    .in(pos),
    .out(out)
);

endmodule
