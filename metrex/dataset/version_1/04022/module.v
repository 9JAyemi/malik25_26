module top_module (
    input [3:0] in, // 4-bit binary input
    output [15:0] out // 16-bit output from the decoder
);

wire [3:0] mux_out;
wire [15:0] decoder_out;

mux_4to1 mux (
    .in0(decoder_out[3:0]),
    .in1(decoder_out[7:4]),
    .in2(decoder_out[11:8]),
    .in3(decoder_out[15:12]),
    .select(in[3:2]),
    .out(mux_out)
);

decoder dec (
    .in(in),
    .out(decoder_out)
);

assign out = mux_out;

endmodule

module mux_4to1(
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] select,
    output reg [3:0] out
);

always @*
begin
    case (select)
        2'b00: out = in0;
        2'b01: out = in1;
        2'b10: out = in2;
        2'b11: out = in3;
    endcase
end

endmodule

module decoder (
    input [3:0] in,
    output [15:0] out
);

assign out = 16'b0000000000000001 << in;

endmodule