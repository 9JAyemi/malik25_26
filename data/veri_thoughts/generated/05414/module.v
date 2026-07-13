module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire Cout1, Cout2, Cout3;

    // First adder stage
    full_adder FA1 (.A(A[0]), .B(B[0]), .Cin(Cin), .S(sum[0]), .Cout(Cout1));

    // Second adder stage
    full_adder FA2 (.A(A[1]), .B(B[1]), .Cin(Cout1), .S(sum[1]), .Cout(Cout2));

    // Third adder stage
    full_adder FA3 (.A(A[2]), .B(B[2]), .Cin(Cout2), .S(sum[2]), .Cout(Cout3));

    // Fourth adder stage
    full_adder FA4 (.A(A[3]), .B(B[3]), .Cin(Cout3), .S(sum[3]), .Cout(Cout));

    assign S = sum;

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire sum1, sum2, sum3;

    // XOR gates
    assign sum1 = A ^ B;
    assign sum2 = sum1 ^ Cin;

    // AND gates
    assign Cout = (A & B) | (Cin & sum1);
    assign S = sum2;

endmodule