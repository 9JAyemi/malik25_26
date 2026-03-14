
module my_nand_gate (
    Y   ,
    A   ,
    B   ,
    C   ,
    D   ,
    VPWR,
    VGND
);

    // Module ports
    output Y   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  D   ;
    input  VPWR;
    input  VGND;

    // Local signals
    wire nand0_out_Y      ;

    //                                 Name         Output             Other arguments
    nand                               nand0       (nand0_out_Y      , D, C, B, A             );
    buf                                buf0        (Y                , nand0_out_Y      );

endmodule
