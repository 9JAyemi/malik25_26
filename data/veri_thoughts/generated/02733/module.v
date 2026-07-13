module top_module (
    input [1:0] in,
    output reg [15:0] out,
    output reg select
);

    wire [15:0] decoder_out;
    reg [3:0] select_bit;

    decoder_4to16 decoder(
        .in(in),
        .out(decoder_out)
    );

    always @(*) begin
        case (in)
            2'b00: select_bit = 4'b0001;
            2'b01: select_bit = 4'b0010;
            2'b10: select_bit = 4'b0100;
            2'b11: select_bit = 4'b1000;
        endcase
    end

    always @(*) begin
        out = 16'b0;
        out[select_bit] = 1'b1;
        select = select_bit != 4'b0000;
    end

endmodule

module decoder_4to16 (
    input [1:0] in,
    output reg [15:0] out
);

    always @(*) begin
        case (in)
            2'b00: out = 16'b0000000000000001;
            2'b01: out = 16'b0000000000000010;
            2'b10: out = 16'b0000000000000100;
            2'b11: out = 16'b0000000000001000;
        endcase
    end

endmodule