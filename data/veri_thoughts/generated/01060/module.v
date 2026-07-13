module and4_module (
    output X,
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    and4 base (
        .X(X),
        .A(A),
        .B(B),
        .C(C),
        .D(D),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module and4 (
    output X,
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign X = A & B & C & D & VPWR & VGND & VPB & VNB;

endmodule