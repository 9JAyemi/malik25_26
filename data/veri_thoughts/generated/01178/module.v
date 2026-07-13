module simple_arithmetic_unit(
    input [3:0] a,        // 4-bit input operand A
    input [3:0] b,        // 4-bit input operand B
    input [1:0] op_select, // Operation select: 00 - add, 01 - subtract, 10 - AND
    output reg [3:0] result, // 4-bit result of the operation
    output reg carry_borrow // Carry (for addition) or Borrow (for subtraction) flag
);

    // Combinational logic for arithmetic operations
    always @(*) begin
        case (op_select)
            2'b00: begin // Addition
                {carry_borrow, result} = a + b; // Perform addition
            end
            2'b01: begin // Subtraction
                {carry_borrow, result} = a - b; // Perform subtraction
                // For subtraction, carry_borrow will indicate borrow, which is the inverted carry.
            end
            2'b10: begin // Bitwise AND
                result = a & b; // Perform bitwise AND
                carry_borrow = 0; // No carry or borrow is generated
            end
            default: begin // Default case
                result = 4'b0000; // Default result
                carry_borrow = 0; // Default carry/borrow
            end
        endcase
    end

endmodule
