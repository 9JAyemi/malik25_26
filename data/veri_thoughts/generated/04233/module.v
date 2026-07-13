
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire C1,C2,C3; // Renamed the C to a single bit instead of 4 bits
    
    // First stage of the adder
    full_adder FA0 (
        .A(A[0]),
        .B(B[0]),
        .Cin(1'b0),
        .S(S[0]),
        .Cout(C1) 
    );
    
    // Second stage of the adder
    full_adder FA1 (
        .A(A[1]),
        .B(B[1]),
        .Cin(C1), 
        .S(S[1]),
        .Cout(C2)
    );
    
    // Third stage of the adder
    full_adder FA2 (
        .A(A[2]),
        .B(B[2]),
        .Cin(C2), 
        .S(S[2]),
        .Cout(C3)
    );
    
    // Fourth stage of the adder
    full_adder FA3 (
        .A(A[3]),
        .B(B[3]),
        .Cin(C3), 
        .S(S[3]),
        .Cout(C_out) 
    );

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