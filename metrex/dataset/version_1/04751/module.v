module or4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    // Voltage supply signals
    supply0 VGND;
    supply1 VPWR;
    supply0 VNB;
    supply1 VPB;

    wire or1_out;
    wire or2_out;

    or2 or1 (
        .A(A),
        .B(B),
        .X(or1_out)
    );

    or2 or2 (
        .A(C),
        .B(D),
        .X(or2_out)
    );

    or2 or3 (
        .A(or1_out),
        .B(or2_out),
        .X(X)
    );

endmodule

module or2 (
    input A,
    input B,
    output X
);

    assign X = A | B;

endmodule