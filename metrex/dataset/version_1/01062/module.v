
module sky130_fd_sc_ms__nor2_1 (
    output Y,
    input A,
    input B,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire w1;
    sky130_fd_sc_ms__a211oi_1 U1 (
        .Y(w1),
        .A1(A),
        .A2(B),
        .B1(VPWR),
        .C1(VNB),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    sky130_fd_sc_ms__inv_1 U2 (
        .Y(Y),
        .A(w1),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module sky130_fd_sc_ms__inv_1 (
    output Y,
    input A,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    sky130_fd_sc_ms__a211oi_1 U1 (
        .Y(Y),
        .A1(A),
        .A2(VPWR),
        .B1(VGND),
        .C1(VNB),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module sky130_fd_sc_ms__a211oi_1 (
    output Y,
    input A1,
    input A2,
    input B1,
    input C1,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire NMOS_TB;
    wire NMOS_BA;
    wire NMOS_AB;
    wire PMOS_BC;

    assign NMOS_TB = B1 & C1;
    assign NMOS_BA = A1 & B1;
    assign NMOS_AB = A1 & A2;
    assign PMOS_BC = B1 & C1;

    assign Y = (NMOS_AB | (NMOS_BA & ~PMOS_BC)) | (NMOS_TB & ~A2);

endmodule
