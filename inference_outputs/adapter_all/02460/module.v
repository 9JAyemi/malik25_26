


module sky130_fd_sc_ls__o2111a (
    X ,
    A1,
    A2,
    B1,
    C1,
    D1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;
    input  C1;
    input  D1;

    wire or0_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , A2, A1             );
    and and0 (and0_out_X, B1, C1, or0_out, D1);
    buf buf0 (X         , and0_out_X         );

endmodule
