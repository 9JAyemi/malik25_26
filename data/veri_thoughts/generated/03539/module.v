


module sky130_fd_sc_lp__iso1p (
    X    ,
    A    ,
    SLEEP
);

    output X    ;
    input  A    ;
    input  SLEEP;

    supply1 KAPWR;
    supply0 VGND ;
    supply1 VPB  ;
    supply0 VNB  ;

    or  or0  (X     , A, SLEEP       );

endmodule
