
module sky130_fd_sc_hvl__o21a_1 (
    X,
    A1,
    A2,
    B1
);

    output X;
    input A1;
    input A2;
    input B1;

    wire a1_xored_a2;

    assign a1_xored_a2 = A1 ^ A2;
    assign X = a1_xored_a2 & B1;

endmodule
module custom_module (
    X,
    A1,
    A2,
    B1
);

    output X;
    input A1;
    input A2;
    input B1;

    wire a1_and_a2;
    wire b1_bit0;

    assign a1_and_a2 = A1 & A2;
    assign b1_bit0 = B1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Instantiate the base cell
    sky130_fd_sc_hvl__o21a_1 base (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(b1_bit0)
    );

endmodule