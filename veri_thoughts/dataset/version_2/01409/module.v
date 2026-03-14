
module sky130_fd_sc_lp__a221o (
    X   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    C1  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    // Module ports
    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  C1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    // Local signals
    wire and0_out         ;
    wire and1_out         ;
    wire or0_out_X        ;

    //                                 Name         Output             Other arguments
    and                                and0        (and0_out         , B1, B2                );
    and                                and1        (and1_out         , A1, A2                );
    or                                 or0         (or0_out_X        , and1_out, and0_out, C1);
    buf                                buf0        (X                , or0_out_X             );

endmodule