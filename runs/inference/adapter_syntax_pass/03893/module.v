
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] SUM
);

wire [3:0] CARRY;

// First full adder
full_adder FA0(
    .A(A[0]),
    .B(B[0]),
    .CARRY_IN(1'b0),
    .SUM(SUM[0]),
    .CARRY_OUT(CARRY[0])
);

// Second full adder
full_adder FA1(
    .A(A[1]),
    .B(B[1]),
    .CARRY_IN(CARRY[0]),
    .SUM(SUM[1]),
    .CARRY_OUT(CARRY[1])
);

// Third full adder
full_adder FA2(
    .A(A[2]),
    .B(B[2]),
    .CARRY_IN(CARRY[1]),
    .SUM(SUM[2]),
    .CARRY_OUT(CARRY[2])
);

// Fourth full adder
full_adder FA3(
    .A(A[3]),
    .B(B[3]),
    .CARRY_IN(CARRY[2]),
    .SUM(SUM[3]),
    .CARRY_OUT()
);

endmodule

module full_adder (
    input A,
    input B,
    input CARRY_IN,
    output SUM,
    output CARRY_OUT
);

wire SUM_int;

//assign SUM = A ^ B ^ CARRY_IN;
assign SUM_int = A ^ B ^ CARRY_IN;
assign SUM = SUM_int;
assign CARRY_OUT = (A & B) | (CARRY_IN & (A ^ B));

endmodule
