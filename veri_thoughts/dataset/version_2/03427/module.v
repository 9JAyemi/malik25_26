


module sky130_fd_sc_lp__iso1n (
    X      ,
    A      ,
    SLEEP_B
);

    output X      ;
    input  A      ;
    input  SLEEP_B;

    wire SLEEP;

    not not0 (SLEEP , SLEEP_B        );
    or  or0  (X     , A, SLEEP       );

endmodule
