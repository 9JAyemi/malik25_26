module my_module (
    output X   ,
    input  A1  ,
    input  A2  
);



    // Local signals
    wire and0_out_X       ;

    //                                 Name         Output             Other arguments
    and                                and0        (and0_out_X       , A1, A2                );
    buf                                buf0        (X                , and0_out_X     );

endmodule