
module calculator(
    input wire clk,
    input wire reset,
    input wire [7:0] a,
    input wire [7:0] b,
    input wire [1:0] op,
    output reg [7:0] result,
    output reg valid
);

reg [15:0] temp_result; // Used for multiplication and division

always @ (posedge clk) begin
    if (reset) begin
        result <= 8'b0;
        valid <= 1'b0;
    end else begin
        case (op)
            2'b00: begin // Addition
                temp_result <= a + b;
                result <= temp_result[7:0];
                valid <= 1'b1;
            end
            2'b01: begin // Subtraction
                temp_result <= a - b;
                result <= temp_result[7:0];
                valid <= 1'b1;
            end
            2'b10: begin // Multiplication
                temp_result <= a * b;
                result <= temp_result[15:8];
                valid <= 1'b1;
            end
            2'b11: begin // Division
                if (b == 0) begin
                    result <= 8'b0;
                    valid <= 1'b0;
                end else begin
                    temp_result <= a / b;
                    result <= temp_result[7:0];
                    valid <= 1'b1;
                end
            end
            default: begin // Invalid operation
                result <= 8'b0;
                valid <= 1'b0;
            end
        endcase
    end
end

endmodule
