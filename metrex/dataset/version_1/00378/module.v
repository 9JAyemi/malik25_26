


module sky130_fd_sc_lp__o32a (
    X ,
    A1,
    A2,
    A3,
    B1,
    B2
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  B2;

    wire or0_out   ;
    wire or1_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , A2, A1, A3      );
    or  or1  (or1_out   , B2, B1          );
    and and0 (and0_out_X, or0_out, or1_out);
    buf buf0 (X         , and0_out_X      );

endmodule
