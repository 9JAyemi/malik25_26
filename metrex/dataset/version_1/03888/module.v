
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    input Sel,
    output [3:0] S,
    output Cout
);

    wire [3:0] temp_sum;
    wire temp_carry;

    assign {temp_carry, temp_sum} = Sel ? A - B : A + B + Cin;

    assign S = temp_sum[3:0];
    assign Cout = Sel ? (A[3] ^ B[3] ^ Cin) : temp_carry;

endmodule