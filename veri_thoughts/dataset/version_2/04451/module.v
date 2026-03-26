
module full_adder_2bit(
    input [1:0] A,
    input [1:0] B,
    input Cin,
    output [1:0] S,
    output Cout
);

wire CO1, CO2;

HAHD2X HA1(A[0], B[0], CO1, S[0]);
HAHD2X HA2(A[1], B[1], CO2, S[1]);

assign Cout = CO1 | CO2 | Cin; // Fix: Assign Cout directly

endmodule
module HAHD2X(
    input A,
    input B,
    output CO,
    output S
);

xor gate1(S, A, B);
and gate2(CO, A, B);

endmodule
module or_gate(
    input A,
    input B,
    input C,
    output Y
);

assign Y = A | B | C;

endmodule