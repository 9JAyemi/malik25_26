module logic_operations (
    COUT,
    SUM ,
    A   ,
    B   ,
    CI 
);

    // Module ports
    output COUT;
    output SUM ;
    input  A   ;
    input  B   ;
    input  CI  ;


    // Local signals
    wire xor0_out_SUM         ;
    wire a_b                  ;
    wire a_ci                 ;
    wire b_ci                 ;
    wire or0_out_COUT         ;

    //                           Name          Output                 Other arguments
    xor                          xor0         (xor0_out_SUM         , A, B, CI                );
    buf                          buf0         (SUM                  , xor0_out_SUM    );
    and                          and0         (a_b                  , A, B                    );
    and                          and1         (a_ci                 , A, CI                   );
    and                          and2         (b_ci                 , B, CI                   );
    or                           or0          (or0_out_COUT         , a_b, a_ci, b_ci         );
    buf                          buf1         (COUT                 , or0_out_COUT   );

endmodule