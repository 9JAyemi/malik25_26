


module sky130_fd_sc_ls__and4 (
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

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out_X;

    and and0 (and0_out_X, A, B, C, D     );
    buf buf0 (X         , and0_out_X     );

endmodule
