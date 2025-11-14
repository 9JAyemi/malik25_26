


module sky130_fd_sc_hd__and3 (
    X,
    A,
    B,
    C
);

    output X;
    input  A;
    input  B;
    input  C;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out_X;

    and and0 (and0_out_X, C, A, B        );
    buf buf0 (X         , and0_out_X     );

endmodule
