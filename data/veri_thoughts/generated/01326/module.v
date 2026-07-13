module priority_encoder (
    input [3:0] in,
    output reg [1:0] pos
);
    always @(*) begin
        case (in)
            4'b1000: pos = 2'b11;
            4'b0100: pos = 2'b10;
            4'b0010: pos = 2'b01;
            4'b0001: pos = 2'b00;
            default: pos = 2'b00;
        endcase
    end
endmodule

module counter (
    input clk,
    input reset,
    input enable,
    output reg [7:0] count
);
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= 8'b0;
        end else if (enable) begin
            count <= count + 1;
        end
    end
endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] in,
    output reg [1:0] pos,
    output reg [7:0] out
);
    wire enable;
    reg [7:0] count;

    priority_encoder pe (
        .in(in),
        .pos(pos)
    );

    assign enable = (pos == 2'b11) ? 1 : 0;

    counter cnt (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(count)
    );

    always @(*) begin
        out = count[7:0] * in;
    end
endmodule