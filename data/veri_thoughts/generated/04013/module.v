
module adder(A, B, Cin, S, Cout);
    parameter WIDTH = 4;
    input [WIDTH-1:0] A, B;
    input Cin;
    output [WIDTH-1:0] S;
    output Cout;

    wire [WIDTH:0] C;

    full_adder fa0(.a(A[0]), .b(B[0]), .c(Cin), .sum(S[0]), .carry(C[0]));
    full_adder fa1(.a(A[1]), .b(B[1]), .c(C[0]), .sum(S[1]), .carry(C[1]));
    full_adder fa2(.a(A[2]), .b(B[2]), .c(C[1]), .sum(S[2]), .carry(C[2]));
    full_adder fa3(.a(A[3]), .b(B[3]), .c(C[2]), .sum(S[3]), .carry(C[3]));
    
    assign Cout = C[WIDTH-1];
endmodule
module full_adder(a, b, c, sum, carry);
    input a, b, c;
    output sum, carry;

    assign sum = a ^ b ^ c;
    assign carry = (a & b) | (b & c) | (a & c);
endmodule