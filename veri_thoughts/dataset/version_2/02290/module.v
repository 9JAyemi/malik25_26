module fa1 (
    A, 
    B, 
    CI, 
    S, 
    CO);
   input A;
   input B;
   input CI;
   output S;
   output CO;
   assign S = A ^ B ^ CI;
   assign CO = (A & B) | (CI & (A ^ B));
endmodule

module addsub4 (
    A, 
    B, 
    M, 
    Y);
   input [3:0] A;
   input [3:0] B;
   input M;
   output [3:0] Y;
   wire [3:0] C;
   wire [3:0] S;
   fa1 fa1_0(A[0], B[0], M, S[0], C[0]);
   fa1 fa1_1(A[1], B[1], C[0], S[1], C[1]);
   fa1 fa1_2(A[2], B[2], C[1], S[2], C[2]);
   fa1 fa1_3(A[3], B[3], C[2], S[3], C[3]);
   assign Y = M ? A - B : A + B;
endmodule