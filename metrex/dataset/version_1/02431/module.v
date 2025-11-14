module top_module (
    input [1:0] decoder_in,
    input [3:0] alu_A,
    input [3:0] alu_B,
    input [2:0] alu_OP,
    output reg [3:0] final_output
);

    wire [3:0] alu_output;
    wire [3:0] decoder_out;

    decoder_2to4 decoder(
        .in(decoder_in),
        .out(decoder_out)
    );

    alu_4bit alu(
        .A(alu_A),
        .B(alu_B),
        .OP(alu_OP),
        .out(alu_output)
    );

    always @(*) begin
        case(decoder_out)
            4'b0001: final_output = alu_output[0];
            4'b0010: final_output = alu_output[1];
            4'b0100: final_output = alu_output[2];
            4'b1000: final_output = alu_output[3];
            default: final_output = 4'b0000;
        endcase
    end

endmodule

module decoder_2to4 (
    input [1:0] in,
    output reg [3:0] out
);

    always @(*) begin
        case(in)
            2'b00: out = 4'b0001;
            2'b01: out = 4'b0010;
            2'b10: out = 4'b0100;
            2'b11: out = 4'b1000;
            default: out = 4'b0000;
        endcase
    end

endmodule

module alu_4bit (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output reg [3:0] out
);

    always @(*) begin
        case(OP)
            3'b000: out = A + B;
            3'b001: out = A - B;
            3'b010: out = A & B;
            3'b011: out = A | B;
            3'b100: out = A ^ B;
            3'b101: out = ~A;
            3'b110: out = ~B;
            3'b111: out = 4'b0000;
            default: out = 4'b0000;
        endcase
    end

endmodule