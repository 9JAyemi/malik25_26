module xor3_1 (
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

    assign X = A ^ B ^ C;

endmodule