


module sky130_fd_sc_hd__and2 (
    X,
    A,
    B
);

    output X;
    input  A;
    input  B;

    wire and0_out_X;

    and and0 (and0_out_X, A, B           );
    buf buf0 (X         , and0_out_X     );

endmodule
