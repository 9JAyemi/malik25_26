
module sky130_fd_sc_lp__a21oi_4 (
    Y   , //RTL_INOUT
    A1  , //RTL_INOUT
    A2  , //RTL_INOUT
    B1  , //RTL_INOUT
    VPWR,
    VGND
);

    inout  Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  VPWR;
    input  VGND;

    sky130_fd_sc_lp__a21oi base (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .VPWR(VPWR),
        .VGND(VGND)
    );

endmodule
module sky130_fd_sc_lp__a21oi (
    Y,
    A1,
    A2,
    B1,
    VPWR,
    VGND
);

    output Y;
    input A1;
    input A2;
    input B1;
    input VPWR;
    input VGND;

    wire  t1;
    wire  t2;

    not (t1, A1);
    and (t2, t1, A2);
    nor (Y, t2, B1);

endmodule