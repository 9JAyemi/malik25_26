


module sky130_fd_sc_lp__and4bb (
    X  ,
    A_N,
    B_N,
    C  ,
    D
);

    output X  ;
    input  A_N;
    input  B_N;
    input  C  ;
    input  D  ;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nor0_out  ;
    wire and0_out_X;

    nor nor0 (nor0_out  , A_N, B_N       );
    and and0 (and0_out_X, nor0_out, C, D );
    buf buf0 (X         , and0_out_X     );

endmodule
