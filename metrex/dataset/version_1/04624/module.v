


module sky130_fd_sc_hd__nor4b (
    Y  ,
    A  ,
    B  ,
    C  ,
    D_N
);

    output Y  ;
    input  A  ;
    input  B  ;
    input  C  ;
    input  D_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire not0_out  ;
    wire nor0_out_Y;

    not not0 (not0_out  , D_N              );
    nor nor0 (nor0_out_Y, A, B, C, not0_out);
    buf buf0 (Y         , nor0_out_Y       );

endmodule
