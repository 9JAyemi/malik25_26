
module sky130_fd_sc_h__a22oi_1 (
    Y,
    A1,
    A2,
    B1,
    B2
);

    output Y;
    input A1;
    input A2;
    input B1;
    input B2;

    assign Y = ~(A1 & A2) | ~(B1 & B2);

endmodule

module four_input_gate (
    Y,
    A1,
    A2,
    B1,
    B2
);

    output Y;
    input A1;
    input A2;
    input B1;
    input B2;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    sky130_fd_sc_h__a22oi_1_wrapper base (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module sky130_fd_sc_h__a22oi_1_wrapper (
    Y,
    A1,
    A2,
    B1,
    B2,
    VPWR,
    VGND,
    VPB,
    VNB
);

    output Y;
    input A1;
    input A2;
    input B1;
    input B2;

    // Voltage supply signals
    input VPWR;
    input VGND;
    input VPB;
    input VNB;

    sky130_fd_sc_h__a22oi_1 U1 (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2)
    );

endmodule
