
module simple_calculator(
    input signed [7:0] a, b,
    output reg signed [7:0] add_out, sub_out, mul_out, div_out,
    input [1:0] op
);

    always @ (a, b, op) begin
        case (op)
            2'b00: begin // addition
                add_out <= a + b;
                sub_out <= 0;
                mul_out <= 0;
                div_out <= 0;
            end
            2'b01: begin // subtraction
                add_out <= 0;
                sub_out <= a - b;
                mul_out <= 0;
                div_out <= 0;
            end
            2'b10: begin // multiplication
                add_out <= 0;
                sub_out <= 0;
                mul_out <= a * b;
                div_out <= 0;
            end
            2'b11: begin // division
                add_out <= 0;
                sub_out <= 0;
                mul_out <= 0;
                div_out <= a / b;
            end
        endcase
    end

endmodule