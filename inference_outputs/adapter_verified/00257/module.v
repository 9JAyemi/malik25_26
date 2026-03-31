
module ripple_carry_adder(
    input [3:0] A, B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    wire [3:0] carry;
    full_adder fa0(A[0], B[0], CIN, SUM[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], SUM[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], SUM[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], SUM[3], COUT);

endmodule

module full_adder(
    input A, B, CIN,
    output SUM, COUT
);
    assign SUM = A ^ B ^ CIN;
    assign COUT = ((A & B) | (B & CIN) | (CIN & A));
endmodule
