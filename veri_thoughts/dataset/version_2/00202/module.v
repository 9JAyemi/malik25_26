
module alu (
    input [3:0] A,
    input [3:0] B,
    input [2:0] opcode,
    input carry_in,
    input invert,
    output [3:0] result,
    output carry_out
);

    reg [3:0] temp_result;

    assign carry_out = ((opcode == 3'b000) && ((A[3] & B[3]) | (A[3] & carry_in) | (B[3] & carry_in))) |
                        ((opcode == 3'b001) && ((A[3] & ~B[3] & ~carry_in) | (~A[3] & B[3] & carry_in)));

    always @(*) begin
        case (opcode)
            3'b000: temp_result = A + B + carry_in;
            3'b001: temp_result = A - B - carry_in;
            3'b010: temp_result = A & B;
            3'b011: temp_result = A | B;
            3'b100: temp_result = A ^ B;
            default: temp_result = 4'b0000;
        endcase

        if (invert) begin
            temp_result = ~temp_result;
        end
    end

    assign result = temp_result;

endmodule
