module calculator(
    input [7:0] in1,
    input [7:0] in2,
    input [1:0] opcode,
    output reg [7:0] result,
    output reg overflow
);

reg [8:0] temp;

always @(*)
begin
    overflow <= 0;
    case (opcode)
        2'b00: // addition
        begin
            temp = in1 + in2;
        end
        2'b01: // subtraction
        begin
            temp = in1 - in2;
        end
        2'b10: // multiplication
        begin
            temp = in1 * in2;
        end
        2'b11: // division
        begin
            if (in2 == 0)
            begin
                temp = 0;
                overflow <= 1;
            end
            else
            begin
                temp = in1 / in2;
            end
        end
        default: // invalid opcode
        begin
            temp = 0;
            overflow <= 1;
        end
    endcase
    if (temp > 255 || temp < -256)
        overflow <= 1;
    result <= temp[7:0];
end

endmodule