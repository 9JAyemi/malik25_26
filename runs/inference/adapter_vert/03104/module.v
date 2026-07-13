module OR3_gate (
    input A,
    input B,
    input C,
    output X,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire or_output;
    OR3 or3_inst (
        .X(or_output),
        .A(A),
        .B(B),
        .C(C)
    );

    assign X = or_output;

endmodule

module OR3 (
    input A,
    input B,
    input C,
    output X
);

    assign X = A | B | C;

endmodule