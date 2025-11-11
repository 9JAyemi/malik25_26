module full_adder (
    input A,
    input B,
    input CIN,
    output SUM,
    output COUT
);

    wire C1, S1, C2;
    fa fa1 (
        .A(A),
        .B(B),
        .CI(CIN),
        .S(S1),
        .CO(C1)
    );
    fa fa2 (
        .A(S1),
        .B(C1),
        .CI(1'b0),
        .S(SUM),
        .CO(C2)
    );
    assign COUT = C1 | C2;

endmodule 

module fa (
    input A,
    input B,
    input CI,
    output S,
    output CO
);

    assign {CO, S} = A + B + CI;

endmodule