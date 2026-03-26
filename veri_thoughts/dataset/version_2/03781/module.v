
module O221A (
    Y,
    A1,
    A2,
    B1,
    B2,
    C1
);

    output Y;
    input A1, A2, B1, B2, C1;

    assign Y = (A1 & A2) | (B1 & B2 & C1);

endmodule

module custom_module (
    Y,
    A1,
    A2,
    B1,
    B2,
    C1
);

    output Y;
    input A1, A2, B1, B2, C1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    O221A base (  // Instance of the O221A gate
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2),
        .C1(C1)
    );

endmodule
