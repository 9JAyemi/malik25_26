module nor3 (
    output Y,
    input A,
    input B,
    input C_N
);

    wire Y_wire, A_wire, B_wire, C_N_wire;
    nor3_gate base (
        .Y(Y_wire),
        .A(A_wire),
        .B(B_wire),
        .C_N(C_N_wire)
    );

    assign Y = Y_wire;
    assign A = A_wire;
    assign B = B_wire;
    assign C_N = C_N_wire;

endmodule

module nor3_gate (
    output Y,
    input A,
    input B,
    input C_N
);

    assign Y = ~(A | B | C_N);

endmodule