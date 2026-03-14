module or4_2 (
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    or4 or4_inst (
        .X(X),
        .A(A),
        .B(B),
        .C(C),
        .D(D)
    );

endmodule

module or4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    assign X = A | B | C | D;

endmodule