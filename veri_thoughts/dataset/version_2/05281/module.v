module sky130_fd_sc_lp__inputiso1p (
    X    ,
    A    ,
    SLEEP,
    VPWR ,
    VGND ,
    VPB  ,
    VNB
);

    output X    ;
    input  A    ;
    input  SLEEP;
    input  VPWR ;
    input  VGND ;
    input  VPB  ;
    input  VNB  ;

    wire X_internal;

    assign X = X_internal;

    assign X_internal = (SLEEP == 1'b1) ? 1'b0 : A;

endmodule