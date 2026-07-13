
module custom_module (
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

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire xor1, xor2, xor3, xor4, xor5;

    xnor (xor1, A1, A2, A3, A4, B1);

    assign xor2 = xor1 ^ A2;
    assign xor3 = xor2 ^ A3;
    assign xor4 = xor3 ^ A4;
    assign xor5 = xor4 ^ B1;
    assign X = xor5;

endmodule