


module sky130_fd_sc_hd__and2b (
    X  ,
    A_N,
    B
);

    output X  ;
    input  A_N;
    input  B  ;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire not0_out  ;
    wire and0_out_X;

    not not0 (not0_out  , A_N            );
    and and0 (and0_out_X, not0_out, B    );
    buf buf0 (X         , and0_out_X     );

endmodule
