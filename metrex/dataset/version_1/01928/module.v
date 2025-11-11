module maj3_2 (
    input A,
    input B,
    input C,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    wire majority;
    maj3 base (
        .X(majority),
        .A(A),
        .B(B),
        .C(C),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

    assign X = (majority == 1'b1) ? 1'b1 : 1'b0;

endmodule

module maj3 (
    output X,
    input A,
    input B,
    input C,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign X = (A & B) | (A & C) | (B & C);

endmodule