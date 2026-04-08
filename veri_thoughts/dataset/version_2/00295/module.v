module top_module (
    input [3:0] A,
    input [3:0] B,
    input [2:0] opcode,
    output [3:0] out,
    output zero
);

wire [3:0] alu_out;
reg [3:0] constant_value = 4'hF;

// Instantiate 4-bit ALU
alu_4bit my_alu (
    .A(A),
    .B(B),
    .opcode(opcode),
    .out(alu_out),
    .zero(zero)
);

// Instantiate Bitwise OR module
bitwise_or my_or (
    .A(alu_out),
    .B(constant_value),
    .out(out)
);

endmodule

module alu_4bit (
    input [3:0] A,
    input [3:0] B,
    input [2:0] opcode,
    output [3:0] out,
    output zero
);

reg [3:0] result;

always @(*) begin
    case (opcode)
        3'b000: result = A + B;
        3'b001: result = A - B;
        3'b010: result = A & B;
        3'b011: result = A | B;
        3'b100: result = A ^ B;
        default: result = 4'b0000;
    endcase
end

assign out = result;
assign zero = (result == 4'b0000);

endmodule

module bitwise_or (
    input [3:0] A,
    input [3:0] B,
    output [3:0] out
);

assign out = A | B;

endmodule