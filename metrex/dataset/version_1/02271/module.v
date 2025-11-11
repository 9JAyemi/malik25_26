module calculator(
    input clk,
    input reset,
    input [1:0] op,
    input [7:0] operand1,
    input [7:0] operand2,
    output reg [7:0] result,
    output reg overflow
);

    // Use an intermediate variable for multiplication to capture the full result
    reg [15:0] mult_result;

    always @(posedge clk) begin
        if (reset) begin
            result <= 0;
            overflow <= 0;
        end else begin
            case (op)
                2'b00: begin // Addition
                    {overflow, result} <= operand1 + operand2;
                end
                2'b01: begin // Subtraction
                    {overflow, result} <= {1'b0, operand1} - {1'b0, operand2};
                    overflow <= overflow != result[7] && (operand1[7] != operand2[7]);
                end
                2'b10: begin // Multiplication
                    mult_result <= operand1 * operand2;
                    result <= mult_result[7:0]; // Assign the lower 8 bits to the result
                    overflow <= |mult_result[15:8]; // Overflow if any of the upper 8 bits are set
                end
                2'b11: begin // Division
                    if (operand2 == 0) begin
                        result <= 0; // Define behavior for division by zero
                        overflow <= 1; // Set overflow flag
                    end else begin
                        result <= operand1 / operand2;
                        overflow <= 0; // Overflow is not applicable in normal division
                    end
                end
                default: begin
                    result <= 0;
                    overflow <= 0;
                end
            endcase
        end
    end

endmodule
