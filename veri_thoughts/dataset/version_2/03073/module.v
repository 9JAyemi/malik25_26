module nor3 (
    Y   ,
    A   ,
    B   ,
    C   
);

    // Module ports
    output Y   ;
    input  A   ;
    input  B   ;
    input  C   ;


    // Local signals
    wire nor0_out_Y       ;

    //                                  Name         Output             Other arguments
    nor                                 nor0        (nor0_out_Y       , B, A, C                );
    buf                                 buf0        (Y                , nor0_out_Y      );

endmodule