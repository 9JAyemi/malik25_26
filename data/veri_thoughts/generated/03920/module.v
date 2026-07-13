


module sky130_fd_sc_ms__maj3 (
    X,
    A,
    B,
    C
);

    output X;
    input  A;
    input  B;
    input  C;

    wire or0_out  ;
    wire and0_out ;
    wire and1_out ;
    wire or1_out_X;

    or  or0  (or0_out  , B, A              );
    and and0 (and0_out , or0_out, C        );
    and and1 (and1_out , A, B              );
    or  or1  (or1_out_X, and1_out, and0_out);
    buf buf0 (X        , or1_out_X         );

endmodule
