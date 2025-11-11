


module sky130_fd_sc_hd__o41a (
    X ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    wire or0_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , A4, A3, A2, A1 );
    and and0 (and0_out_X, or0_out, B1    );
    buf buf0 (X         , and0_out_X     );

endmodule
