module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] C;
    
    // Full adder for the least significant bit
    full_adder FA0(
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin),
        .S(S[0]),
        .C(C[0])
    );
    
    // Full adder for the second least significant bit
    full_adder FA1(
        .A(A[1]),
        .B(B[1]),
        .Cin(C[0]),
        .S(S[1]),
        .C(C[1])
    );
    
    // Full adder for the third least significant bit
    full_adder FA2(
        .A(A[2]),
        .B(B[2]),
        .Cin(C[1]),
        .S(S[2]),
        .C(C[2])
    );
    
    // Full adder for the most significant bit
    full_adder FA3(
        .A(A[3]),
        .B(B[3]),
        .Cin(C[2]),
        .S(S[3]),
        .C(Cout)
    );
    
endmodule

// Full adder module
module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output C
);

    wire w1, w2, w3;
    
    // XOR gate to calculate the sum
    xor(S, A, B, Cin);
    
    // AND gate to calculate the carry
    and(w1, A, B);
    and(w2, A, Cin);
    and(w3, B, Cin);
    or(C, w1, w2, w3);
    
endmodule