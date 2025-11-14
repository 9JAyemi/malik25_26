
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input CI,
    output [3:0] SUM,
    output CO
);

    wire C1, C2, C3;

    // Instantiate 4-bit full adder cells
    full_adder FA0(A[0], B[0], CI, SUM[0], C1);
    full_adder FA1(A[1], B[1], C1, SUM[1], C2);
    full_adder FA2(A[2], B[2], C2, SUM[2], C3);
    full_adder FA3(A[3], B[3], C3, SUM[3], CO);

endmodule

module full_adder (
    input A,
    input B,
    input CI,
    output SUM,
    output CO
);

    // Assign Sum and Carry Out using XOR and AND gates
    assign SUM = A ^ B ^ CI;
    assign CO = (A & B) | (B & CI) | (A & CI);

endmodule
