


module sky130_fd_sc_hdll__isobufsrc (
    X    ,
    SLEEP,
    A
);

    output X    ;
    input  SLEEP;
    input  A    ;

    wire not0_out  ;
    wire and0_out_X;

    not not0 (not0_out  , SLEEP          );
    and and0 (and0_out_X, not0_out, A    );
    buf buf0 (X         , and0_out_X     );

endmodule
