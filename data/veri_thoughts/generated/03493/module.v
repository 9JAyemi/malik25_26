
module sky130_fd_sc_hs__o311ai_2 (
    Y ,
    A1,
    A2,
    A3,
    B1,
    C1
);
    output  Y ;
    input   A1;
    input   A2;
    input   A3;
    input   B1;
    input   C1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    // Logic implementation
    sky130_fd_sc_hd__o311ai_1 o311ai_1 (
        .Y ( Y ),
        .A1 ( A1 ),
        .A2 ( A2 ),
        .A3 ( A3 ),
        .B1 ( B1 ),
        .C1 ( C1 )
    );

endmodule

module sky130_fd_sc_hd__o311ai_1 (
    Y,
    A1,
    A2,
    A3,
    B1,
    C1
);
    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  C1;

    // Logic implementation
    assign Y = (A1 & A2 & A3) | (B1 & C1);

endmodule
