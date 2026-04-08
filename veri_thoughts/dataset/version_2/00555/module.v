module ripple_carry_adder (input [3:0] A, input [3:0] B, input Ci, output [3:0] S, output Co);
    wire [3:0] C;

    full_adder FA0 (.A(A[0]), .B(B[0]), .Ci(Ci), .S(S[0]), .Co(C[1]));
    full_adder FA1 (.A(A[1]), .B(B[1]), .Ci(C[1]), .S(S[1]), .Co(C[2]));
    full_adder FA2 (.A(A[2]), .B(B[2]), .Ci(C[2]), .S(S[2]), .Co(C[3]));
    full_adder FA3 (.A(A[3]), .B(B[3]), .Ci(C[3]), .S(S[3]), .Co(Co));
endmodule

module full_adder (
    input A, 
    input B, 
    input Ci, 
    output S, 
    output Co
);
    assign {Co, S} = A + B + Ci;
endmodule