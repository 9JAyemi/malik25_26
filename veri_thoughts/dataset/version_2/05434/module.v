


module sky130_fd_sc_hdll__or2 (
    X,
    A,
    B
);

    output X;
    input  A;
    input  B;

    wire or0_out_X;

    or  or0  (or0_out_X, B, A           );
    buf buf0 (X        , or0_out_X      );

endmodule
