module simple_calculator(
    input [7:0] A,
    input [7:0] B,
    input [1:0] opcode,
    output reg [7:0] result
);

always @(*) begin
    case (opcode)
        2'b00: result = A + B; // addition
        2'b01: result = A - B; // subtraction
        2'b10: result = A * B; // multiplication
        2'b11: result = A / B; // division
    endcase
end

endmodule