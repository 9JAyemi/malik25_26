
module mux_4to2 (
    X ,
    A0,
    A1,
    A2,
    A3,
    S0,
    S1
);

    output X ;
    input  A0;
    input  A1;
    input  A2;
    input  A3;
    input  S0;
    input  S1;

    wire   X_inner;

    mux2_1 U0_mux_0 (
        .A0(A0),
        .A1(A1),
        .S(S0),
        .X(X_inner)
    );

    mux2_1 U1_mux_0 (
        .A0(X_inner),
        .A1(A2),
        .S(S1),
        .X(X)
    );

endmodule
module mux2_1 (
    A0,
    A1,
    S,
    X
);

    output X ;
    input  A0;
    input  A1;
    input  S;

    assign X = (S) ? A1 : A0;

endmodule