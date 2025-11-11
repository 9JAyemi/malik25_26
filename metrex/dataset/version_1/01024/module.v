


module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg (
    X      ,
    A      ,
    SLEEP_B
);

    output X      ;
    input  A      ;
    input  SLEEP_B;

    wire SLEEP     ;
    wire and0_out_X;

    not not0 (SLEEP     , SLEEP_B        );
    and and0 (and0_out_X, SLEEP_B, A     );
    buf buf0 (X         , and0_out_X     );

endmodule
