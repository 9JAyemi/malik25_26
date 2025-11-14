module calculator(
    input clk,
    input rst,
    input [1:0] op,
    input [7:0] num1,
    input [7:0] num2,
    output reg [7:0] result,
    output reg overflow,
    output reg divide_by_zero
);

reg [15:0] product;
reg [15:0] quotient;
reg [15:0] dividend;
reg [7:0] divisor;

always @(posedge clk) begin
    if (rst) begin
        result <= 8'b0;
        overflow <= 1'b0;
        divide_by_zero <= 1'b0;
    end
    else begin
        case (op)
            2'b00: begin // addition
                result <= num1 + num2;
                overflow <= (result[7] != num1[7]) && (result[7] != num2[7]);
                divide_by_zero <= 1'b0;
            end
            2'b01: begin // subtraction
                result <= num1 - num2;
                overflow <= (result[7] != num1[7]) && (result[7] == num2[7]);
                divide_by_zero <= 1'b0;
            end
            2'b10: begin // multiplication
                product <= num1 * num2;
                if (product[15:8] != 8'b0) begin // overflow
                    overflow <= 1'b1;
                    result <= 8'b0;
                end
                else begin
                    overflow <= 1'b0;
                    result <= product[7:0];
                end
                divide_by_zero <= 1'b0;
            end
            2'b11: begin // division
                if (num2 == 8'b0) begin // divide by zero
                    divide_by_zero <= 1'b1;
                    result <= 8'b0;
                end
                else begin
                    divide_by_zero <= 1'b0;
                    dividend <= {num1, 8'b0};
                    divisor <= {num2, 8'b0};
                    quotient <= dividend / divisor;
                    if (quotient[15:8] != 8'b0) begin // overflow
                        overflow <= 1'b1;
                        result <= 8'b0;
                    end
                    else begin
                        overflow <= 1'b0;
                        result <= quotient[7:0];
                    end
                end
            end
        endcase
    end
end

endmodule