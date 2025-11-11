


module sky130_fd_sc_lp__iso0n (
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

    and and0 (X     , A, SLEEP_B     );

endmodule
