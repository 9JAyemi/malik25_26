
module calculator_fixed(input [3:0] num1, input [3:0] num2, input [1:0] op, input clk, input rst, output [3:0] result, output [3:0] display);

reg [7:0] temp_result;
reg [3:0] temp_display;

always @(posedge clk) begin
    if (rst) begin
        temp_result <= 0;
        temp_display <= 0;
    end else begin
        case (op)
            2'b00: begin // addition
                temp_result <= num1 + num2;
            end
            2'b01: begin // subtraction
                temp_result <= num1 - num2;
            end
            2'b10: begin // multiplication
                temp_result <= num1 * num2;
            end
            2'b11: begin // division
                temp_result <= num1 / num2;
            end
        endcase
        case (op)
            2'b00: begin // addition
                temp_display <= {1'b0, temp_result[3:0]}; // Corrected to add leading zero for addition
            end
            2'b01: begin // subtraction
                if (temp_result[7]) begin // Negative number
                    temp_display <= {1'b1, temp_result[3:0]}; // Corrected to add negative sign for negative numbers
                end else begin // Positive number
                    temp_display <= {1'b0, temp_result[3:0]}; // Corrected to add leading zero for positive numbers
                end
            end
            2'b10: begin // multiplication
                temp_display <= temp_result[3:0]; // Corrected to remove leading zero for multiplication
            end
            2'b11: begin // division
                temp_display <= {1'b0, temp_result[3:0]}; // Corrected to add leading zero for division
            end
        endcase
    end
end

assign result = temp_result[3:0];
assign display = temp_display;

endmodule