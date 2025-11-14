


module sky130_fd_sc_ls__and3b (
    X  ,
    A_N,
    B  ,
    C
);

    output X  ;
    input  A_N;
    input  B  ;
    input  C  ;

    wire not0_out  ;
    wire and0_out_X;

    not not0 (not0_out  , A_N            );
    and and0 (and0_out_X, C, not0_out, B );
    buf buf0 (X         , and0_out_X     );

endmodule
