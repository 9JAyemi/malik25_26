module top_module (
    input [2:0] A, // Inputs for 3-to-8 decoder
    input [3:0] in, // Inputs for 4-to-16 decoder
    output [7:0] q // 8-bit output from functional module
);

    wire [7:0] dec_3to8;
    wire [15:0] dec_4to16;

    decoder_3to8 dec3to8(.A(A), .Y(dec_3to8));
    decoder_4to16 dec4to16(.in(in), .out(dec_4to16));
    functional_module func(.dec_3to8(~dec_3to8), .dec_4to16(dec_4to16), .q(q));

endmodule

module decoder_3to8 (
    input [2:0] A,
    output reg [7:0] Y
);
    always @*
    begin
        case(A)
            3'b000: Y = 8'b11111110;
            3'b001: Y = 8'b11111101;
            3'b010: Y = 8'b11111011;
            3'b011: Y = 8'b11110111;
            3'b100: Y = 8'b11101111;
            3'b101: Y = 8'b11011111;
            3'b110: Y = 8'b10111111;
            3'b111: Y = 8'b01111111;
            default: Y = 8'b00000000;
        endcase
    end

endmodule

module decoder_4to16 (
    input [3:0] in,
    output reg [15:0] out
);
    always @*
    begin
        case(in)
            4'b0000: out = 16'b0000000000000001;
            4'b0001: out = 16'b0000000000000010;
            4'b0010: out = 16'b0000000000000100;
            4'b0011: out = 16'b0000000000001000;
            4'b0100: out = 16'b0000000000010000;
            4'b0101: out = 16'b0000000000100000;
            4'b0110: out = 16'b0000000001000000;
            4'b0111: out = 16'b0000000010000000;
            4'b1000: out = 16'b0000000100000000;
            4'b1001: out = 16'b0000001000000000;
            4'b1010: out = 16'b0000010000000000;
            4'b1011: out = 16'b0000100000000000;
            4'b1100: out = 16'b0001000000000000;
            4'b1101: out = 16'b0010000000000000;
            4'b1110: out = 16'b0100000000000000;
            4'b1111: out = 16'b1000000000000000;
            default: out = 16'b0000000000000000;
        endcase
    end

endmodule

module functional_module (
    input [7:0] dec_3to8, // Active-low outputs of 3-to-8 decoder
    input [15:0] dec_4to16, // Active-high outputs of 4-to-16 decoder
    output reg [7:0] q // 8-bit output from bitwise OR operation
);
    always @*
    begin
        q = dec_3to8 | dec_4to16[15:8];
    end

endmodule