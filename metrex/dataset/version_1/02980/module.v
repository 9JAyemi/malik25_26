


module sky130_fd_sc_hd__lpflow_inputiso1p (
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

    or  or0  (X     , A, SLEEP       );

endmodule
