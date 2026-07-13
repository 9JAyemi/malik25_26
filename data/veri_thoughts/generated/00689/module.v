module ALU #(parameter N=32)(
    input [3:0] op_code,
    input signed [N-1:0] operand1,
    input signed [N-1:0] operand2,
    input clk,
    output reg signed [N-1:0] result,
    output reg zero,
    output reg overflow
    );
    
    always @(posedge clk) begin
        case(op_code)
            0: begin //SLL
                result = operand2 << operand1[4:0];
                zero = (result == 0);
                overflow = 0;
            end
            1: begin //SRL
                result = operand2 >> operand1[4:0];
                zero = (result == 0);
                overflow = 0;
            end
            2: begin //SRA
                result = operand2 >>> operand1[4:0];
                zero = (result == 0);
                overflow = 0;
            end
            3: begin //ADD
                result = operand1 + operand2;
                zero = (result == 0);
                overflow = (result[N-1] != operand1[N-1] && result[N-1] != operand2[N-1]);
            end
            4: begin //SUB
                result = operand1 - operand2;
                zero = (result == 0);
                overflow = (result[N-1] != operand1[N-1] && result[N-1] == operand2[N-1]);
            end
            5: begin //AND
                result = operand1 & operand2;
                zero = (result == 0);
                overflow = 0;
            end
            6: begin //OR
                result = operand1 | operand2;
                zero = (result == 0);
                overflow = 0;
            end
            7: begin //XOR
                result = operand1 ^ operand2;
                zero = (result == 0);
                overflow = 0;
            end
            8: begin //NOR
                result = ~(operand1 | operand2);
                zero = (result == 0);
                overflow = 0;
            end
            9: begin //SLT
                result = (operand1 < operand2);
                zero = (result == 0);
                overflow = 0;
            end
            default: begin
                result = 0;
                zero = 0;
                overflow = 0;
            end
        endcase
    end

endmodule