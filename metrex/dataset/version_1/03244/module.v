module mux4to1 (
    A   ,
    B   ,
    C   ,
    D   ,
    S0  ,
    S1  ,
    Y   
);

    // Module ports
    input  A  ;
    input  B  ;
    input  C  ;
    input  D  ;
    input  S0 ;
    input  S1 ;
    output Y  ;

    // Local signals
    wire not_S0_out  ;
    wire not_S1_out  ;
    wire and1_out    ;
    wire and2_out    ;
    wire and3_out    ;
    wire and4_out    ;
    wire or1_out     ;

    //                                 Name        Output             Other arguments
    not                                not_S0     (not_S0_out        , S0                    );
    not                                not_S1     (not_S1_out        , S1                    );
    and                                and1       (and1_out          , A, not_S0_out, not_S1_out);
    and                                and2       (and2_out          , B, not_S0_out, S1       );
    and                                and3       (and3_out          , C, S0, not_S1_out       );
    and                                and4       (and4_out          , D, S0, S1              );
    or                                 or1        (Y                 , and1_out, and2_out, and3_out, and4_out);

endmodule