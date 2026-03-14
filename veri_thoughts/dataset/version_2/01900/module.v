
module sky130_fd_sc_hdll__or2 (
    AB,
    A,
    B,
    VPWR,
    VGND
);

    output AB;
    input A;
    input B;

    // Voltage supply signals
    input VPWR;
    input VGND;

    assign AB = A | B;

endmodule
module or4_top_module (
    X,
    A,
    B,
    C,
    D_N,
    VPWR,
    VGND,
    VPB,
    VNB
);

    output X;
    input A;
    input B;
    input C;
    input D_N;

    // Voltage supply signals
    input VPWR;
    input VGND;
    input VPB ;
    input VNB ;

    wire AB;
    wire CD;

    sky130_fd_sc_hdll__or2 or2_1(
        .AB(AB),
        .A(A),
        .B(B),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    sky130_fd_sc_hdll__or2 or2_2(
        .AB(CD),
        .A(C),
        .B(D_N),
        .VPWR(VPWR),
        .VGND(VGND)
    );

    sky130_fd_sc_hdll__or2 or2_3(
        .AB(X),
        .A(AB),
        .B(CD),
        .VPWR(VPWR),
        .VGND(VGND)
    );

endmodule