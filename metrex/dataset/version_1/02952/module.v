
module top_module( 
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output [5:0] out_not
); 

    wire [7:0] or_bitwise;
    wire or_logical;
    wire [2:0] not_a;
    wire [2:0] not_b;

    assign or_bitwise = a | b; // Fixed the instantiation of decoder_module
    assign or_logical = a ^ b; // Fixed the instantiation of xor_module
    assign not_a = ~a; // Fixed the instantiation of not_decoder
    assign not_b = ~b; // Fixed the instantiation of not_decoder2

    assign out_or_bitwise = or_bitwise[2:0];
    assign out_or_logical = or_logical;
    assign out_not = {not_b, not_a};

endmodule

module decoder_module(
    input [2:0] in,
    output reg [7:0] out
);

    always @(*) begin
        case(in)
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

module xor_module(
    input a,
    input b,
    output reg out
);

    always @(a, b) begin
        out = a ^ b;
    end

endmodule
