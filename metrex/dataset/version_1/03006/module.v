


module sky130_fd_sc_hd__a311o (
    X ,
    A1,
    A2,
    A3,
    B1,
    C1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  C1;

    wire and0_out ;
    wire or0_out_X;

    and and0 (and0_out , A3, A1, A2      );
    or  or0  (or0_out_X, and0_out, C1, B1);
    buf buf0 (X        , or0_out_X       );

endmodule
