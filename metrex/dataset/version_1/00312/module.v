module calculator(
    input clk,
    input [7:0] A,
    input [7:0] B,
    input [1:0] op,
    output reg [7:0] result,
    output reg overflow,
    output reg underflow
);

    // Temporary variable for multiplication to check for overflow
    reg [15:0] temp_mul;

    always @(posedge clk) begin
        overflow <= 0; // Default to no overflow
        underflow <= 0; // Default to no underflow

        case(op)
            2'b00: begin // Addition
                result <= A + B;
                overflow <= ((A[7] == B[7]) && (result[7] != A[7]));
            end
            2'b01: begin // Subtraction
                result <= A - B;
                overflow <= ((A[7] != B[7]) && (result[7] != A[7]));
                underflow <= ((A < B) && (A[7] == 0) && (B[7] == 0));
            end
            2'b10: begin // Multiplication
                temp_mul <= A * B; 
                result <= temp_mul[7:0];
                overflow <= (temp_mul[15:8] != 0); 
            end
            2'b11: begin // Division
                if (B == 8'b0) begin
                    result <= 8'b0; 
                    underflow <= 1; 
                end else begin
                    result <= A / B;
                end
            end
            default: begin
                result <= 8'b0;
            end
        endcase
    end
endmodule
