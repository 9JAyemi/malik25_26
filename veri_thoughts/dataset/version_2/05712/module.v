
module adder4 (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);

    wire [3:0] C;
    wire [3:0] S1;
    wire [3:0] S2;
    wire [3:0] S3;
    
    full_adder fa1 (
        .A(A[0]),
        .B(B[0]),
        .Cin(1'b0),
        .S(S1[0]),
        .Cout(C[0])
    );
    
    full_adder fa2 (
        .A(A[1]),
        .B(B[1]),
        .Cin(C[0]),
        .S(S2[1]),
        .Cout(C[1])
    );
    
    full_adder fa3 (
        .A(A[2]),
        .B(B[2]),
        .Cin(C[1]),
        .S(S3[2]),
        .Cout(C[2])
    );
    
    full_adder fa4 (
        .A(A[3]),
        .B(B[3]),
        .Cin(C[2]),
        .S(S[3]),
        .Cout(Cout)
    );
    
    assign S[0] = S1[0];
    assign S[1] = S2[1];
    assign S[2] = S3[2];
    assign S[3] = S[3];

endmodule
module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign {Cout, S} = A + B + Cin;

endmodule