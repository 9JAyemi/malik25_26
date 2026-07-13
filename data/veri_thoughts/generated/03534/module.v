
module my_module (
    X ,
    A1,
    A2,
    B1,
    C1
);

    output X ;
    input  A1;
    input  A2;
    input  B1;
    input  C1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Gate level implementation.
    wire X_int;
    nand2 nand2_1 (
        .A1(A1),
        .A2(A2),
        .Y(X_int)
    );
    nor2 nor2_1 (
        .A1(B1),
        .A2(C1),
        .Y(X)
    );

endmodule

module nand2 (
    A1,
    A2,
    Y
);

    input A1, A2;
    output Y;

    assign Y = ~(A1 & A2);

endmodule

module nor2 (
    A1,
    A2,
    Y
);

    input A1, A2;
    output Y;

    assign Y = ~(A1 | A2);

endmodule
