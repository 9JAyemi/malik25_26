
module mux_4_1 (
    Y,
    A,
    B,
    C,
    D,
    S0,
    S1
);

    output Y;
    input A;
    input B;
    input C;
    input D;
    input S0;
    input S1;

    wire w1, w2;

    mux2_1 mux1 (
        .Y(w1),
        .A(A),
        .B(B),
        .S(S0)
    );

    mux2_1 mux2 (
        .Y(w2),
        .A(C),
        .B(D),
        .S(S0)
    );

    mux2_1 mux3 (
        .Y(Y),
        .A(w1),
        .B(w2),
        .S(S1)
    );

endmodule

module mux2_1 (
    Y,
    A,
    B,
    S
);

    output Y;
    input A;
    input B;
    input S;

    assign Y = S ? B : A;

endmodule
