module alu_4bit (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output reg [3:0] result
);

    always @(*) begin
        case (OP)
            3'b000: result = A + B; // Addition
            3'b001: result = A - B; // Subtraction
            3'b010: result = A & B; // Bitwise AND
            3'b011: result = A | B; // Bitwise OR
            3'b100: result = A ^ B; // Bitwise XOR
            3'b101: result = A << 1; // Arithmetic Shift Left
            default: result = 4'bxxxx; // Invalid OP code
        endcase
    end

endmodule