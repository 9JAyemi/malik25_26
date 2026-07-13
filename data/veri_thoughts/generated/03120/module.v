
module sky130_fd_sc_hvl__inv_1 (
    Y,
    A,
    VPWR,
    VGND
);

    output Y;
    input A;
    input VPWR;
    input VGND;

    wire nA;

    // Inverter
    assign nA = ~A;
    assign Y = nA;

endmodule

module sky130_fd_sc_hvl__nand3_1 (
    Y,
    A,
    B,
    C,
    VPWR,
    VGND
);

    output Y;
    input A, B, C;
    input VPWR, VGND;

    wire nA, nB, nC, nY;

    // Inverters
    assign nA = ~A;
    assign nB = ~B;
    assign nC = ~C;

    // NAND gate
    assign nY = nA & nB & nC;
    assign Y = ~nY;

endmodule

module sky130_fd_sc_hvl__a21oi_1 (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    VPWR,
    VGND
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  VPWR;
    input  VGND;

    wire nA1, nA2, nB1;

    // Inverters
    sky130_fd_sc_hvl__inv_1 U1 (.Y(nA1), .A(A1), .VPWR(VPWR), .VGND(VGND));
    sky130_fd_sc_hvl__inv_1 U2 (.Y(nA2), .A(A2), .VPWR(VPWR), .VGND(VGND));
    sky130_fd_sc_hvl__inv_1 U3 (.Y(nB1), .A(B1), .VPWR(VPWR), .VGND(VGND));

    // 3-input NAND gate
    sky130_fd_sc_hvl__nand3_1 U4 (.Y(Y), .A(nA1), .B(nA2), .C(nB1), .VPWR(VPWR), .VGND(VGND));

endmodule

module my_module (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    VPWR,
    VGND
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  VPWR;
    input  VGND;

    sky130_fd_sc_hvl__a21oi_1 U5 (.Y(Y), .A1(A1), .A2(A2), .B1(B1), .VPWR(VPWR), .VGND(VGND));

endmodule
