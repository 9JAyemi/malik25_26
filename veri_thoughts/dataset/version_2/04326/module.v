


module sky130_fd_sc_ls__o221a (
    X ,
    A1,
    A2,
    B1,
    B2,
    C1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;
    input  C1;

    wire or0_out   ;
    wire or1_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , B2, B1              );
    or  or1  (or1_out   , A2, A1              );
    and and0 (and0_out_X, or0_out, or1_out, C1);
    buf buf0 (X         , and0_out_X          );

endmodule
