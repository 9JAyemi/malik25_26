
module sky130_fd_sc_hs__and2_1 (
    X   ,
    A   ,
    B   ,
    VPWR,
    VGND
);

    output X   ;
    input  A   ;
    input  B   ;
    input  VPWR;
    input  VGND;

    wire X_int;

    sky130_fd_sc_hs__and2_1_comb and2 (
        .X(X_int),
        .A(A),
        .B(B)
    );

    assign X = ~X_int;

endmodule

module sky130_fd_sc_hs__and2_1_comb (
    X   ,
    A   ,
    B   
);

    output X   ;
    input  A   ;
    input  B   ;

    assign X = A & B;

endmodule

module sky130_fd_sc_hs__nand2_1 (
    Y   ,
    A   ,
    B   ,
    VPWR,
    VGND
);

    output Y   ;
    input  A   ;
    input  B   ;
    input  VPWR;
    input  VGND;

    wire A_int;
    wire B_int;

    assign A_int = ~A;
    assign B_int = ~B;

    sky130_fd_sc_hs__and2_1_comb and2 (
        .X(Y),
        .A(A_int),
        .B(B_int)
    );

endmodule

module sky130_fd_sc_hs__and3b_1 (
    X   ,
    A   ,
    B   ,
    C   ,
    VPWR,
    VGND
);

    output X   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  VPWR;
    input  VGND;

    wire AB;
    wire ABC;

    sky130_fd_sc_hs__and2_1_comb and1 (
        .X(AB),
        .A(A),
        .B(B)
    );

    sky130_fd_sc_hs__nand2_1_comb nand2 (
        .Y(ABC),
        .A(AB),
        .B(C)
    );

    assign X = ABC;

endmodule

module sky130_fd_sc_hs__nand2_1_comb (
    Y   ,
    A   ,
    B   
);

    output Y   ;
    input  A   ;
    input  B   ;

    assign Y = ~(A & B);

endmodule
