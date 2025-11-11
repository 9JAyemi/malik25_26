module simple_calculator(
    input clk,
    input rst,
    input [1:0] op,
    input signed [7:0] num1,
    input signed [7:0] num2,
    output reg signed [7:0] result,
    output reg overflow
);

always @(posedge clk) begin
    if (rst) begin
        result <= 0;
        overflow <= 0;
    end
    else begin
        case (op)
            2'b00: begin // addition
                result <= num1 + num2;
                overflow <= ((num1[7] == num2[7]) && (result[7] != num1[7]));
            end
            2'b01: begin // subtraction
                result <= num1 - num2;
                overflow <= ((num1[7] != num2[7]) && (result[7] != num1[7]));
            end
            2'b10: begin // multiplication
                result <= num1 * num2;
                overflow <= ((result[7:0] != 0) && (result[7:0] != -1));
            end
            2'b11: begin // division
                if (num2 == 0) begin
                    result <= 0;
                    overflow <= 1;
                end
                else begin
                    result <= num1 / num2;
                    overflow <= 0;
                end
            end
        endcase
    end
end

endmodule