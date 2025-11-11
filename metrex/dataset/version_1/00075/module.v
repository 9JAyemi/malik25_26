
module sky130_fd_sc_lp__nand2_4 (
    X ,
    A1,
    A2,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;

    wire A3, A4;

    sky130_fd_sc_lp__inv_2 U1 (
        .Y(A3),
        .A(A1)
    );

    sky130_fd_sc_lp__inv_2 U2 (
        .Y(A4),
        .A(A2)
    );

    sky130_fd_sc_lp__nand2_1 U3 (
        .X(X),
        .A1(A3),
        .A2(A4),
        .B1(B1)
    );

endmodule

module sky130_fd_sc_lp__o41a_m (
    X ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    wire X_tmp;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    sky130_fd_sc_lp__nand2_4 base (
        .X(X_tmp),
        .A1(A1),
        .A2(A2),
        .B1(B1)
    );

    assign X = ~X_tmp;

endmodule

module sky130_fd_sc_lp__inv_2 (
    Y ,
    A
);

    output Y ;
    input  A;

    wire A_temp;

    assign A_temp = ~A;

    assign Y = A_temp;

endmodule

module sky130_fd_sc_lp__nand2_1 (
    X ,
    A1,
    A2,
    B1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;

    wire A1_temp, A2_temp, B1_temp;

    assign A1_temp = ~A1;
    assign A2_temp = ~A2;
    assign B1_temp = ~B1;

    assign X = (A1_temp & A2_temp) | B1_temp;

endmodule
