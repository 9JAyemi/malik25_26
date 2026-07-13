module four_bit_adder(
    output [3:0] S,
    output C_out,
    input [3:0] A,
    input [3:0] B
);

    wire [3:0] XOR_out;
    wire [3:0] AND_out;
    wire [3:0] carry;

    xor_gate XOR0(.Y(XOR_out[0]), .A(A[0]), .B(B[0]));
    xor_gate XOR1(.Y(XOR_out[1]), .A(A[1]), .B(B[1]));
    xor_gate XOR2(.Y(XOR_out[2]), .A(A[2]), .B(B[2]));
    xor_gate XOR3(.Y(XOR_out[3]), .A(A[3]), .B(B[3]));

    and_gate AND0(.Y(AND_out[0]), .A(XOR_out[0]), .B(XOR_out[1]));
    and_gate AND1(.Y(AND_out[1]), .A(XOR_out[2]), .B(XOR_out[3]));
    and_gate AND2(.Y(AND_out[2]), .A(XOR_out[1]), .B(XOR_out[2]));
    and_gate AND3(.Y(AND_out[3]), .A(XOR_out[0]), .B(XOR_out[1]));

    xor_gate XOR4(.Y(S[0]), .A(XOR_out[0]), .B(XOR_out[1]));
    xor_gate XOR5(.Y(S[1]), .A(XOR_out[2]), .B(XOR_out[3]));
    xor_gate XOR6(.Y(S[2]), .A(XOR_out[1]), .B(XOR_out[2]));
    xor_gate XOR7(.Y(S[3]), .A(S[2]), .B(AND_out[0]));

    and_gate AND4(.Y(carry[0]), .A(AND_out[0]), .B(AND_out[1]));
    and_gate AND5(.Y(carry[1]), .A(AND_out[2]), .B(AND_out[3]));
    and_gate AND6(.Y(carry[2]), .A(AND_out[1]), .B(AND_out[2]));
    or_gate  OR0 (.Y(C_out), .A(carry[0]), .B(carry[1]), .C(carry[2]));

endmodule

module xor_gate(
    output Y,
    input A,
    input B
);
    assign Y = A ^ B;
endmodule

module and_gate(
    output Y,
    input A,
    input B
);
    assign Y = A & B;
endmodule

module or_gate(
    output Y,
    input A,
    input B,
    input C
);
    assign Y = A | B | C;
endmodule