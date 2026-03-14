module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] sum;
wire C1, C2, C3;

// Full adders
full_adder F1(.A(A[0]), .B(B[0]), .Cin(Cin), .S(sum[0]), .Cout(C1));
full_adder F2(.A(A[1]), .B(B[1]), .Cin(C1), .S(sum[1]), .Cout(C2));
full_adder F3(.A(A[2]), .B(B[2]), .Cin(C2), .S(sum[2]), .Cout(C3));
full_adder F4(.A(A[3]), .B(B[3]), .Cin(C3), .S(sum[3]), .Cout(Cout));

assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

assign S = A ^ B ^ Cin;
assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule