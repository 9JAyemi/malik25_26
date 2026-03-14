module add_4bit(
    input [3:0] A,
    input [3:0] B,
    output [4:0] C
);

    wire [3:0] S;
    wire C0, C1, C2;
    
    // First full adder
    full_adder fa1 (
        .a(A[0]),
        .b(B[0]),
        .c_in(1'b0),
        .s(S[0]),
        .c_out(C0)
    );
    
    // Second full adder
    full_adder fa2 (
        .a(A[1]),
        .b(B[1]),
        .c_in(C0),
        .s(S[1]),
        .c_out(C1)
    );
    
    // Third full adder
    full_adder fa3 (
        .a(A[2]),
        .b(B[2]),
        .c_in(C1),
        .s(S[2]),
        .c_out(C2)
    );
    
    // Fourth full adder
    full_adder fa4 (
        .a(A[3]),
        .b(B[3]),
        .c_in(C2),
        .s(S[3]),
        .c_out(C[4])
    );
    
    assign C[3:0] = S;
    assign C[4] = C[4];
    
endmodule

module full_adder(
    input a,
    input b,
    input c_in,
    output s,
    output c_out
);

    assign s = a ^ b ^ c_in;
    assign c_out = (a & b) | (a & c_in) | (b & c_in);
    
endmodule