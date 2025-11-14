
module my_alu #(
    parameter N = 8 // Parameter to define the number of bits
)(
    input signed [N-1:0] a,
    input signed [N-1:0] b,
    input [3:0] op,
    output signed [N-1:0] result,
    output carry
);


reg signed [N-1:0] result_reg;
reg carry_reg;

always @* begin
    case(op)
        4'b0000: begin // a + b
            result_reg = a + b;
            carry_reg = (result_reg[N-1] == a[N-1] && result_reg[N-1] == b[N-1]) ? 1 : 0;
        end
        4'b0001: begin // a - b
            result_reg = a - b;
            carry_reg = (result_reg[N-1] == a[N-1] && result_reg[N-1] != b[N-1]) ? 1 : 0;
        end
        4'b0010: begin // a & b
            result_reg = a & b;
            carry_reg = 0;
        end
        4'b0011: begin // a | b
            result_reg = a | b;
            carry_reg = 0;
        end
        4'b0100: begin // a ^ b
            result_reg = a ^ b;
            carry_reg = 0;
        end
        4'b0101: begin // ~a
            result_reg = ~a;
            carry_reg = 0;
        end
        4'b0110: begin // ~b
            result_reg = ~b;
            carry_reg = 0;
        end
        4'b0111: begin // 0
            result_reg = 0;
            carry_reg = 0;
        end
        4'b1000: begin // a << b
            result_reg = a << b;
            carry_reg = (result_reg[N-1] == 1) ? 1 : 0;
        end
        4'b1001: begin // a >> b
            result_reg = a >> b;
            carry_reg = (result_reg[0] == 1) ? 1 : 0;
        end
        4'b1010: begin // a >>> b
            result_reg = $signed({a[N-1], a}) >>> b;
            carry_reg = (result_reg[0] == 1) ? 1 : 0;
        end
        4'b1011: begin // a == b
            result_reg = (a == b) ? 1 : 0;
            carry_reg = 0;
        end
        4'b1100: begin // a != b
            result_reg = (a != b) ? 1 : 0;
            carry_reg = 0;
        end
        4'b1101: begin // a > b
            result_reg = (a > b) ? 1 : 0;
            carry_reg = 0;
        end
        4'b1110: begin // a >= b
            result_reg = (a >= b) ? 1 : 0;
            carry_reg = 0;
        end
        4'b1111: begin // a < b
            result_reg = (a < b) ? 1 : 0;
            carry_reg = 0;
        end
    endcase
end

assign result = result_reg;
assign carry = carry_reg;

endmodule
