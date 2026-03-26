module sky130_fd_sc_hs__a22oi (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    VPWR,
    VGND
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;

    assign Y = (~A1 & ~A2 & B1) | (~A1 & A2 & B2) | (A1 & ~A2 & B2) | (A1 & A2 & ~B1); 

endmodule

module sky130_fd_sc_hs__a22oi_4 (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    VPWR,
    VGND
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;
    sky130_fd_sc_hs__a22oi base (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2),
        .VPWR(VPWR),
        .VGND(VGND)
    );

endmodule