


module sky130_fd_sc_lp__o22a (
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

    wire or0_out   ;
    wire or1_out   ;
    wire and0_out_X;

    or  or0  (or0_out   , A2, A1          );
    or  or1  (or1_out   , B2, B1          );
    and and0 (and0_out_X, or0_out, or1_out);
    buf buf0 (X         , and0_out_X      );

endmodule
