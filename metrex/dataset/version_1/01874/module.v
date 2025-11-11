module and_pg (
    A   ,
    B   ,
    PG  
);

    // Module ports
    input  A   ;
    input  B   ;
    output PG  ;

    // Local signals
    wire  and_out        ;

    //                                 Name         Output             Other arguments
    and                                and0        (and_out          , A, B    );
    buf                                buf0       (PG               , and_out         );

endmodule