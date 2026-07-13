


module sky130_fd_sc_lp__iso1n (
    X      ,
    A      ,
    SLEEP_B
);

    output X      ;
    input  A      ;
    input  SLEEP_B;

    supply1 VPWR ;
    supply0 KAGND;
    supply1 VPB  ;
    supply0 VNB  ;

    wire SLEEP;

    not not0 (SLEEP , SLEEP_B        );
    or  or0  (X     , A, SLEEP       );

endmodule
