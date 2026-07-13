


module sky130_fd_sc_ls__or2 (
    X,
    A,
    B
);

    output X;
    input  A;
    input  B;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire or0_out_X;

    or  or0  (or0_out_X, B, A           );
    buf buf0 (X        , or0_out_X      );

endmodule
