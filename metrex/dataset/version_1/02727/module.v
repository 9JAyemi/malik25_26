
module calculator (
    input [3:0] num1,
    input [3:0] num2,
    input [1:0] op_type,
    output [7:0] result,
    output overflow
);

    wire [7:0] adder_out;
    wire [7:0] multiplier_out;
    wire [7:0] num1_extended;
    wire [7:0] num2_extended;
    wire [3:0] highest_bit_num1;
    wire [3:0] highest_bit_num2;
    wire [3:0] highest_bit;
    wire [7:0] zero;
    assign zero = 8'b0;
    assign overflow = (adder_out[7] == adder_out[6] && adder_out[6] != op_type[0]);

    // Convert 4-bit numbers to 8-bit numbers
    assign num1_extended = {4'b0, num1};
    assign num2_extended = {4'b0, num2};

    // Priority encoder to detect highest bit
    assign highest_bit_num1 = (num1_extended[7]) ? 4'b1000 :
                             (num1_extended[6]) ? 4'b0100 :
                             (num1_extended[5]) ? 4'b0010 :
                             (num1_extended[4]) ? 4'b0001 :
                             4'b0000;
    assign highest_bit_num2 = (num2_extended[7]) ? 4'b1000 :
                             (num2_extended[6]) ? 4'b0100 :
                             (num2_extended[5]) ? 4'b0010 :
                             (num2_extended[4]) ? 4'b0001 :
                             4'b0000;
    assign highest_bit = (highest_bit_num1 > highest_bit_num2) ? highest_bit_num1 : highest_bit_num2;

    // Carry-lookahead adder for addition and subtraction
    CLA_adder adder(
        .A(num1_extended),
        .B(num2_extended),
        .Cin(op_type[0]),
        .Sum(adder_out),
        .Cout()
    );

    // Repeated addition for multiplication
    assign multiplier_out = (op_type[1]) ? num1_extended * num2_extended : 8'b0;

    // Select final output based on operation type
    assign result = (op_type == 2'b00) ? adder_out :
                    (op_type == 2'b01) ? adder_out :
                    multiplier_out;

endmodule
module CLA_adder (
    input [7:0] A,
    input [7:0] B,
    input Cin,
    output [7:0] Sum,
    output Cout
);

    wire [7:0] P;
    wire [7:0] G;
    wire [7:0] C;
    wire [7:0] C_propagate;
    wire [7:0] C_generate;

    assign P = A ^ B;
    assign G = A & B;
    assign C_propagate[0] = Cin;
    assign C_generate[0] = G[0];
    generate
        genvar i;
        for (i = 1; i < 8; i = i + 1) begin : generate_CLA
            assign C_propagate[i] = P[i-1];
            assign C_generate[i] = G[i] | (P[i] & C_generate[i-1]);
        end
    endgenerate

    assign C = C_propagate | C_generate;
    assign Sum = P ^ Cin;
    assign Cout = C[7];

endmodule