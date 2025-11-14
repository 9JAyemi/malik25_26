


module sky130_fd_sc_hdll__o21a (
    X ,
    A1,
    A2,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;

    wire or0_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , A2, A1         );
    and and0 (and0_out_X, or0_out, B1    );
    buf buf0 (X         , and0_out_X     );

endmodule
