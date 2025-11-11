
module decoder_bcd (
    input [3:0] binary_in,
    output reg [3:0] out_high,
    output reg [3:0] out_low
);

    wire [15:0] decoder_out;
    wire [3:0] bcd_out;
    
    decoder_4to16 decoder_inst (
        .in(binary_in),
        .out(decoder_out)
    );
    
    bcd_encoder bcd_inst (
        .in(decoder_out),
        .out(bcd_out)
    );
    
    always @(*) begin
        out_high = bcd_out[3:0];
        out_low = bcd_out[3:0];
    end

endmodule
module decoder_4to16 (
    input [3:0] in,
    output reg [15:0] out
);

    always @* begin
        case (in)
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
module bcd_encoder (
    input [15:0] in,
    output reg [3:0] out
);

    always @* begin
        case (in)
            16'b0000000000000001: out = 4'b0001;
            16'b0000000000000010: out = 4'b0010;
            16'b0000000000000100: out = 4'b0011;
            16'b0000000000001000: out = 4'b0100;
            16'b0000000000010000: out = 4'b0101;
            16'b0000000000100000: out = 4'b0110;
            16'b0000000001000000: out = 4'b0111;
            16'b0000000010000000: out = 4'b1000;
            16'b0000000100000000: out = 4'b1001;
            16'b0000001000000000: out = 4'b0001;
            16'b0000010000000000: out = 4'b0010;
            16'b0000100000000000: out = 4'b0011;
            16'b0001000000000000: out = 4'b0100;
            16'b0010000000000000: out = 4'b0101;
            16'b0100000000000000: out = 4'b0110;
            16'b1000000000000000: out = 4'b0111;
            default: out = 4'b0000;
        endcase
    end

endmodule
module top_module (
    input A,
    input B,
    input C,
    input D,
    output reg [3:0] out_high,
    output reg [3:0] out_low
);

    decoder_bcd decoder_inst (
        .binary_in({A, B, C, D}),
        .out_high(out_high),
        .out_low(out_low)
    );

endmodule