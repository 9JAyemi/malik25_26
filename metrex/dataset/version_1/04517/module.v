
module top_module (
    input [2:0] ABC,
    input EN,
    output reg [7:0] Y
);

    wire [3:0] binary_sum;
    wire [2:0] decoder_input;
    wire [7:0] decoder_output;

    binary_adder adder(.X(ABC), .Y(4'b0001), .S(binary_sum));
    assign decoder_input = binary_sum[2:0];
    decoder decoder(.ABC(decoder_input), .EN(EN), .Y(decoder_output));

    always @(*) begin
        case(decoder_output)
            3'b000: Y = 8'b11000000;
            3'b001: Y = 8'b11111001;
            3'b010: Y = 8'b10100100;
            3'b011: Y = 8'b10110000;
            3'b100: Y = 8'b10011001;
            3'b101: Y = 8'b10010010;
            3'b110: Y = 8'b10000010;
            3'b111: Y = 8'b11111000;
            default: Y = 8'b00000000;
        endcase
    end

endmodule
module binary_adder (
    input [2:0] X,
    input [3:0] Y,
    output reg [3:0] S
);
    always @(*) begin
        S = X + Y;
    end
endmodule
module decoder (
    input [2:0] ABC,
    input EN,
    output reg [7:0] Y
);
    always @(*) begin
        case({ABC, EN})
            4'b0001: Y = 8'b11000000;
            4'b0010: Y = 8'b11111001;
            4'b0011: Y = 8'b10100100;
            4'b0100: Y = 8'b10110000;
            4'b0101: Y = 8'b10011001;
            4'b0110: Y = 8'b10010010;
            4'b0111: Y = 8'b10000010;
            4'b1000: Y = 8'b11111000;
            default: Y = 8'b00000000;
        endcase
    end
endmodule