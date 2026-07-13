


module sky130_fd_sc_lp__iso0p (
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

    wire sleepn;

    not not0 (sleepn, SLEEP          );
    and and0 (X     , A, sleepn      );

endmodule
