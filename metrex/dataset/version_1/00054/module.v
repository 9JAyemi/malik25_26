


module sky130_fd_sc_lp__nor3b (
    Y  ,
    A  ,
    B  ,
    C_N
);

    output Y  ;
    input  A  ;
    input  B  ;
    input  C_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nor0_out  ;
    wire and0_out_Y;

    nor nor0 (nor0_out  , A, B           );
    and and0 (and0_out_Y, C_N, nor0_out  );
    buf buf0 (Y         , and0_out_Y     );

endmodule
