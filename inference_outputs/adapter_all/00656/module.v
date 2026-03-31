
module or3_4_custom (
    X,
    A,
    B,
    C
);

    output X;
    input  A;
    input  B;
    input  C;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    sky130_fd_sc_lp__or3_4 base (
        .X(X),
        .A(A),
        .B(B),
        .C(C)
    );

endmodule

module sky130_fd_sc_lp__or3_4 (
    X,
    A,
    B,
    C
);

    output X;
    input  A;
    input  B;
    input  C;

    assign X = A | B | C;

endmodule
