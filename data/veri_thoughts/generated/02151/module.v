module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] C; // Internal carry signals
    wire [3:0] X; // Internal sum signals
    
    // Full adder module instance
    full_adder FA0(.A(A[0]), .B(B[0]), .Cin(Cin), .S(X[0]), .C(C[0]));
    full_adder FA1(.A(A[1]), .B(B[1]), .Cin(C[0]), .S(X[1]), .C(C[1]));
    full_adder FA2(.A(A[2]), .B(B[2]), .Cin(C[1]), .S(X[2]), .C(C[2]));
    full_adder FA3(.A(A[3]), .B(B[3]), .Cin(C[2]), .S(X[3]), .C(C[3]));

    // Output signals
    assign S = X;
    assign Cout = C[3];

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output C
);

    assign S = A ^ B ^ Cin;
    assign C = (A & B) | (A & Cin) | (B & Cin);

endmodule