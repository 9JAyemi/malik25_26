
module ripple_carry_adder (
    S,
    Cout,
    A,
    B,
    Cin
);

    output [3:0] S;
    output Cout;
    input [3:0] A;
    input [3:0] B;
    input Cin;

    wire [3:0] carry_out;
    wire [3:0] sum;

    // Instantiate full adders
    full_adder fa0(
        .S(sum[0]),
        .Cout(carry_out[0]),
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin)
    );

    full_adder fa1(
        .S(sum[1]),
        .Cout(carry_out[1]),
        .A(A[1]),
        .B(B[1]),
        .Cin(carry_out[0])
    );

    full_adder fa2(
        .S(sum[2]),
        .Cout(carry_out[2]),
        .A(A[2]),
        .B(B[2]),
        .Cin(carry_out[1])
    );

    full_adder fa3(
        .S(sum[3]),
        .Cout(Cout),
        .A(A[3]),
        .B(B[3]),
        .Cin(carry_out[2])
    );

    // Assign sum output
    assign S = sum;

endmodule

module full_adder (
    S,
    Cout,
    A,
    B,
    Cin
);

    output S;
    output Cout;
    input A;
    input B;
    input Cin;

    wire sum1;
    wire sum2;

    // XOR gates
    xor (sum1, A, B);
    xor (S, sum1, Cin);

    // AND gate
    and (sum2, A, B);

    // OR gate
    or (Cout, sum2, Cin);

endmodule
