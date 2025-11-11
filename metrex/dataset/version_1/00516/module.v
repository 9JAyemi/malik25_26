
module top_module (
    input clk,
    input reset, // synchronous active-high reset
    output reg [15:0] out,
    output [1:0] count
);

    // 2-bit synchronous up-counter
    reg [1:0] counter;
    always @(posedge clk) begin
        if (reset) begin
            counter <= 2'b00;
        end else begin
            counter <= counter + 1;
        end
    end
    assign count = counter;

    // 3-to-8 decoder
    wire [2:0] decoder_in;
    assign decoder_in = counter;
    wire [7:0] decoder_out;
    decoder_3to8 decoder_inst (
        .in(decoder_in),
        .out(decoder_out)
    );

    // additional logic gates to implement 4-to-16 decoder
    wire [15:0] decoder_out_16;
    assign decoder_out_16 = {decoder_out[0], decoder_out[0], decoder_out[0], decoder_out[0], decoder_out[1], decoder_out[1], decoder_out[1], decoder_out[1], decoder_out[2], decoder_out[2], decoder_out[2], decoder_out[2], decoder_out[3], decoder_out[3], decoder_out[3], decoder_out[3]};

    // final output module
    reg [15:0] out_reg = decoder_out_16;
    always @(posedge clk) out <= out_reg;

endmodule
module decoder_3to8 (
    input [2:0] in,
    output reg [7:0] out
);
    always @(*) begin
        case (in)
            3'b000: out = 8'b00000001;
            3'b001: out = 8'b00000010;
            3'b010: out = 8'b00000100;
            3'b011: out = 8'b00001000;
            3'b100: out = 8'b00010000;
            3'b101: out = 8'b00100000;
            3'b110: out = 8'b01000000;
            3'b111: out = 8'b10000000;
            default: out = 8'b00000000;
        endcase
    end
endmodule