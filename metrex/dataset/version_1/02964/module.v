


module sky130_fd_sc_ls__or3b (
    X  ,
    A  ,
    B  ,
    C_N
);

    output X  ;
    input  A  ;
    input  B  ;
    input  C_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire not0_out ;
    wire or0_out_X;

    not not0 (not0_out , C_N            );
    or  or0  (or0_out_X, B, A, not0_out );
    buf buf0 (X        , or0_out_X      );

endmodule
