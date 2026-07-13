


module sky130_fd_sc_hdll__and2 (
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

    wire and0_out_X;

    and and0 (and0_out_X, A, B           );
    buf buf0 (X         , and0_out_X     );

endmodule
