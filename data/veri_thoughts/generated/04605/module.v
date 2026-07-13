module sky130_fd_sc_hd__and4bb (
    //# {{data|Data Signals}}
    input  A_N,
    input  B_N,
    input  C  ,
    input  D  ,
    output X
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Internal signals
    wire A, B, Y1, Y2;

    // Invert the input signals
    not #(2) na (A, A_N);
    not #(2) nb (B, B_N);

    // AND the input signals
    and #(2) n1 (Y1, A, B);
    and #(2) n2 (Y2, C, D);

    // AND the intermediate signals
    and #(2) n3 (X, Y1, Y2);

endmodule