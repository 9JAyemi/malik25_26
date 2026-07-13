module sky130_fd_sc_lp__o221ai (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    C1  ,
    VPWR,
    VGND
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  C1  ;
    input  VPWR;
    input  VGND;

    assign Y = A1 & A2 & B1 & B2 & C1 & VPWR & VGND;

endmodule