
module sky130_fd_sc_hs__a31o (
    VPWR,
    VGND,
    X,
    A1,
    A2,
    A3,
    B1
);
    // Module ports
    input  VPWR;
    input  VGND;
    output X;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    // Internal logic
    wire n1, n2, n3;

    // Instantiate submodules
    sky130_fd_sc_hs__and2_1 and2_1 (
        .A(A1),
        .B(A2),
        .X(n1)
    );

    sky130_fd_sc_hs__and2_1 and2_2 (
        .A(n1),
        .B(A3),
        .X(n2)
    );

    sky130_fd_sc_hs__and2_1 and2_3 (
        .A(B1),
        .B(n2),
        .X(n3)
    );

    // Output assignment
    assign X = n3;

endmodule

module sky130_fd_sc_hs__a31o_wrapper (
    VPWR,
    VGND,
    Y,
    A1,
    A2,
    A3,
    B1,
    SEL
);

    // Module ports
    input  VPWR;
    input  VGND;
    output Y;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  SEL;

    // Local signals
    wire X;
    wire not_X;

    // Instantiate submodules
    sky130_fd_sc_hs__a31o a31o_inst (
        .VPWR(VPWR),
        .VGND(VGND),
        .X(X),
        .A1(A1),
        .A2(A2),
        .A3(A3),
        .B1(B1)
    );

    // Output assignment
    assign not_X = ~X;

    assign Y = (SEL == 1'b0) ? X : not_X;

endmodule

module sky130_fd_sc_hs__and2_1 (
    A,
    B,
    X
);
    // Module ports
    input  A;
    input  B;
    output X;

    // Internal logic
    wire n1;

    // Instantiate submodules
    sky130_fd_sc_hs__nand2_1 nand2_1 (
        .A(A),
        .B(B),
        .Y(n1)
    );

    // Output assignment
    assign X = ~n1;

endmodule

module sky130_fd_sc_hs__nand2_1 (
    A,
    B,
    Y
);
    // Module ports
    input  A;
    input  B;
    output Y;

    // Internal logic
    wire n1;

    // Instantiate submodules
    sky130_fd_sc_hs__nor2_1 nor2_1 (
        .A(A),
        .B(B),
        .Y(n1)
    );

    // Output assignment
    assign Y = ~n1;

endmodule

module sky130_fd_sc_hs__nor2_1 (
    A,
    B,
    Y
);
    // Module ports
    input  A;
    input  B;
    output Y;

    // Logic logic
    assign Y = ~(A | B);

endmodule
