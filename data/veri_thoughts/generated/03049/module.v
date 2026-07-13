module full_adder(input A, input B, input Cin, output S, output Cout);
    wire w1, w2, w3;
    assign w1 = A ^ B;
    assign w2 = A & B;
    assign w3 = w2 | (Cin & w1);
    assign S = w1 ^ Cin;
    assign Cout = w3;
endmodule

module adder_8bit(input [7:0] A, input [7:0] B, output [7:0] S, output Cout);
    wire [7:0] w1, w2, w3, w4, w5, w6, w7, w8;
    full_adder fa0(.A(A[0]), .B(B[0]), .Cin(1'b0), .S(w1[0]), .Cout(w2[0]));
    full_adder fa1(.A(A[1]), .B(B[1]), .Cin(w2[0]), .S(w1[1]), .Cout(w2[1]));
    full_adder fa2(.A(A[2]), .B(B[2]), .Cin(w2[1]), .S(w1[2]), .Cout(w2[2]));
    full_adder fa3(.A(A[3]), .B(B[3]), .Cin(w2[2]), .S(w1[3]), .Cout(w2[3]));
    full_adder fa4(.A(A[4]), .B(B[4]), .Cin(w2[3]), .S(w1[4]), .Cout(w2[4]));
    full_adder fa5(.A(A[5]), .B(B[5]), .Cin(w2[4]), .S(w1[5]), .Cout(w2[5]));
    full_adder fa6(.A(A[6]), .B(B[6]), .Cin(w2[5]), .S(w1[6]), .Cout(w2[6]));
    full_adder fa7(.A(A[7]), .B(B[7]), .Cin(w2[6]), .S(w1[7]), .Cout(w2[7]));
    assign S = {w1[7], w1[6], w1[5], w1[4], w1[3], w1[2], w1[1], w1[0]};
    assign Cout = w2[7];
endmodule