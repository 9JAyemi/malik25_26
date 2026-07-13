module decoder(
    input wire [1:0] in,
    output wire [1:0] out
);

assign out = (in == 2'b00) ? 2'b00 :
             (in == 2'b01) ? 2'b01 :
             (in == 2'b10) ? 2'b10 : 2'b11;

endmodule

module split_16bit_input(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    wire [1:0] select;
    wire [1:0] decoder_out;

    // Decoder to select which output to use
    decoder dec1 (
        .in(select),
        .out(decoder_out)
    );

    // Multiplexer to select the output
    assign out_hi = decoder_out[0] ? in[15:8] : in[7:0];
    assign out_lo = decoder_out[1] ? in[15:8] : in[7:0];

    // Select line for the decoder
    assign select = in[15];

endmodule