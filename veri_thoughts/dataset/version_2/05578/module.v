


module sky130_fd_sc_lp__a22o (
    X ,
    A1,
    A2,
    B1,
    B2
);

    output X ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out ;
    wire and1_out ;
    wire or0_out_X;

    and and0 (and0_out , B1, B2            );
    and and1 (and1_out , A1, A2            );
    or  or0  (or0_out_X, and1_out, and0_out);
    buf buf0 (X        , or0_out_X         );

endmodule
