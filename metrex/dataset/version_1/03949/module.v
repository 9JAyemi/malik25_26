


module sky130_fd_sc_ls__a31o (
    X ,
    A1,
    A2,
    A3,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out ;
    wire or0_out_X;

    and and0 (and0_out , A3, A1, A2     );
    or  or0  (or0_out_X, and0_out, B1   );
    buf buf0 (X        , or0_out_X      );

endmodule
