module my_module (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  B1  ,
    input  C1  ,
    input  D1  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    // Module ports
    //output X   ;
    //input  A1  ;
    //input  A2  ;
    //input  B1  ;
    //input  C1  ;
    //input  D1  ;
    //input  VPWR;
    //input  VGND;
    //input  VPB ;
    //input  VNB ;

    // Local signals
    wire and0_out         ;
    wire or0_out_X        ;
    wire pwrgood_pp0_out_X;

    //                                 Name         Output             Other arguments
    and                                and0        (and0_out         , A1, A2               );
    or                                 or0         (or0_out_X        , C1, B1, and0_out, D1 );
    //sky130_fd_sc_ms__udp_pwrgood_pp$PG pwrgood_pp0 (pwrgood_pp0_out_X, or0_out_X, VPWR, VGND);
    buf                                buf0        (X                , or0_out_X           );

endmodule