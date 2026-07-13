
module RippleCarryAdder (
    input wire [3:0] A,
    input wire [3:0] B,
    input wire CIN,
    output wire [3:0] S,
    output wire COUT
);

    wire [3:0] co;

    FullAdder FA0(.A(A[0]), .B(B[0]), .CIN(CIN), .COUT(co[0]), .SUM(S[0]));
    FullAdder FA1(.A(A[1]), .B(B[1]), .CIN(co[0]), .COUT(co[1]), .SUM(S[1]));
    FullAdder FA2(.A(A[2]), .B(B[2]), .CIN(co[1]), .COUT(co[2]), .SUM(S[2]));
    FullAdder FA3(.A(A[3]), .B(B[3]), .CIN(co[2]), .COUT(COUT), .SUM(S[3]));

endmodule

module FullAdder (
    input wire A,
    input wire B,
    input wire CIN,
    output wire COUT,
    output wire SUM
);

    wire p, g;

    assign p = A ^ B;
    assign g = A & B;

    assign SUM = p ^ CIN;
    assign COUT = g | (p & CIN);

endmodule
