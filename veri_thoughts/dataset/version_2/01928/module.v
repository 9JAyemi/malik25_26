module my_nor (
    Y   ,
    A   ,
    B   ,
    C  ,
);

    // Module ports
    output Y   ;
    input  A   ;
    input  B   ;
    input  C   ;


    // Local signals
    wire nor0_out_Y       ;
    wire nor1_out_Y       ;

    //                                 Name         Output             Other arguments
    nor                                nor0        (nor0_out_Y       , A, B               );
    nor                                nor1        (nor1_out_Y       , C, nor0_out_Y      );
    buf                                buf0        (Y                , nor1_out_Y     );

endmodule
