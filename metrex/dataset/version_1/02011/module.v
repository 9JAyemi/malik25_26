module adder_subtractor_4bit (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output [3:0] SUM
);

wire [3:0] CIN;
wire [3:0] COUT;

assign CIN[0] = SUB;
assign CIN[1] = COUT[0];
assign CIN[2] = COUT[1];
assign CIN[3] = COUT[2];

fa fa0 (
    .A(A[0]),
    .B(B[0]),
    .CIN(CIN[0]),
    .SUM(SUM[0]),
    .COUT(COUT[0])
);
fa fa1 (
    .A(A[1]),
    .B(B[1]),
    .CIN(CIN[1]),
    .SUM(SUM[1]),
    .COUT(COUT[1])
);
fa fa2 (
    .A(A[2]),
    .B(B[2]),
    .CIN(CIN[2]),
    .SUM(SUM[2]),
    .COUT(COUT[2])
);
fa fa3 (
    .A(A[3]),
    .B(B[3]),
    .CIN(CIN[3]),
    .SUM(SUM[3]),
    .COUT(COUT[3])
);

endmodule

module fa (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

assign {COUT, SUM} = A + B + CIN;

endmodule