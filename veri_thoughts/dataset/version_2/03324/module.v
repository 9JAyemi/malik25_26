


module sky130_fd_sc_hdll__inputiso0p (
    X    ,
    A    ,
    SLEEP
);

    output X    ;
    input  A    ;
    input  SLEEP;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire sleepn;

    not not0 (sleepn, SLEEP          );
    and and0 (X     , A, sleepn      );

endmodule
