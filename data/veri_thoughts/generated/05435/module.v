
module four_input_nand_gate (
    Y   ,
    A_N ,
    B   ,
    C   ,
    D   
);

    // Module ports
    output Y   ;
    input  A_N ;
    input  B   ;
    input  C   ;
    input  D   ;

    // Local signals
    wire not0_out         ;
    wire nand0_out_Y      ;

    //                                   Name         Output             Other arguments
    not                                  not0        (not0_out         , A_N                    );
    nand                                 nand0       (nand0_out_Y      , D, C, B, not0_out      );
    buf                                  buf0        (Y                , nand0_out_Y      );

endmodule