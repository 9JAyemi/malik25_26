
module sky130_fd_sc_lp__and2 (
    X   ,
    A   ,
    B   ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    // Module ports
    output X   ;
    input  A   ;
    input  B   ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    // Local signals
    wire and0_out_X       ;

    //                                 Name         Output             Other arguments
    and                                and0        (and0_out_X       , A, B                  );
    buf                                buf0        (X                , and0_out_X     );

endmodule
