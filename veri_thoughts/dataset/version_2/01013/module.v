


module sky130_fd_sc_ls__or4 (
    X,
    A,
    B,
    C,
    D
);

    output X;
    input  A;
    input  B;
    input  C;
    input  D;

    wire or0_out_X;

    or  or0  (or0_out_X, D, C, B, A     );
    buf buf0 (X        , or0_out_X      );

endmodule
