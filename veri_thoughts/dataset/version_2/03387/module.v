module split_bytes(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    wire [7:0] shifted_in = in >> 8; // Shift input right by 8 bits to get upper byte
    wire [7:0] mux_out;

    // Multiplexer selects between shifted input and lower byte of input
    assign mux_out = (in[7:0] == 8'b0) ? shifted_in : in[7:0];

    assign out_hi = shifted_in;
    assign out_lo = mux_out;

endmodule

module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    split_bytes split_bytes_inst(
        .in(in),
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

endmodule