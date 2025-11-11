
module multiplier_alu_top (
    input [7:0] A,
    input [7:0] B,
    input [2:0] OP,
    output reg [7:0] final_output
);

    // 8-bit multiplier module
    wire [15:0] mult_result;
    multiplier_8bit mult_inst (
        .A(A),
        .B(B),
        .P(mult_result)
    );

    // 4-bit ALU module
    wire [3:0] alu_result;
    alu_4bit alu_inst (
        .A(mult_result[7:4]), // Truncate the MSB 4 bits of the multiplication result
        .B(A[3:0]), // Truncate the MSB 4 bits of A
        .OP(OP),
        .Y(alu_result)
    );

    // Additive functional module
    always @ (*) //Changed from always @ (mult_result or alu_result)
    begin
        final_output = mult_result[15:8] + alu_result;
    end

endmodule

module multiplier_8bit (
    input [7:0] A,
    input [7:0] B,
    output reg [15:0] P
);

    reg [8:0] sum; //Changed the width from 16 to 9
    integer i; //Declare i as an integer for the loop

    always @ (*) //Changed from always @ (A or B)
    begin
        P = 0;
        sum = 0;
        for (i = 0; i < 8; i = i + 1)
        begin
            if (B[i] == 1)
            begin
                sum = sum + (A << i);
            end
        end
        P = sum[7:0]; //Truncate the MSB 8 bits
    end

endmodule

module alu_4bit (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output reg [3:0] Y
);

    always @ (*) //Changed from always @ (A or B or OP)
    begin
        case (OP)
            3'b000: Y = A + B; // addition
            3'b001: Y = A - B; // subtraction
            3'b010: Y = A & B; // bitwise AND
            3'b011: Y = A | B; // bitwise OR
            3'b100: Y = A ^ B; // bitwise XOR
            3'b101: Y = A << 1; // arithmetic shift left
            default: Y = 0;
        endcase
    end

endmodule
