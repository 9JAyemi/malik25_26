module my_module (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  B1  ,
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
    //input  VPWR;
    //input  VGND;
    //input  VPB ;
    //input  VNB ;

    // Local signals
    wire and0_out         ;
    wire or0_out_X        ;
    wire pwrgood_pp0_out_X;

    // Module instances
    and and0 (and0_out, A1, A2);
    or or0 (or0_out_X, and0_out, B1);
    //sky130_fd_sc_hdll__udp_pwrgood_pp$PG pwrgood_pp0 (pwrgood_pp0_out_X, or0_out_X, VPWR, VGND);
    buf buf0 (X, or0_out_X);

endmodule