module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);

always @* begin
    if (in[7]) pos = 3'b111; // MSB is high
    else if (in[6]) pos = 3'b110; // Bit 6 is high
    else if (in[5]) pos = 3'b101; // Bit 5 is high
    else if (in[4]) pos = 3'b100; // Bit 4 is high
    else if (in[3]) pos = 3'b011; // Bit 3 is high
    else if (in[2]) pos = 3'b010; // Bit 2 is high
    else if (in[1]) pos = 3'b001; // Bit 1 is high
    else pos = 3'b000; // No bits are high
end

endmodule

module top_module (
    input [7:0] in,
    output [2:0] pos
);

wire [2:0] pe_pos;

priority_encoder pe(
    .in(in),
    .pos(pe_pos)
);

assign pos = pe_pos;

endmodule