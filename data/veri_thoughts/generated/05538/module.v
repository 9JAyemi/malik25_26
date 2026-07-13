


module sky130_fd_sc_ms__o21ba (
    X   ,
    A1  ,
    A2  ,
    B1_N
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nor0_out  ;
    wire nor1_out_X;

    nor nor0 (nor0_out  , A1, A2         );
    nor nor1 (nor1_out_X, B1_N, nor0_out );
    buf buf0 (X         , nor1_out_X     );

endmodule
