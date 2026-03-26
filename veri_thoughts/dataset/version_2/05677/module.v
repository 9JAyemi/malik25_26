module mux_2_1 (
    Y,
    A,
    B,
    S
);

    output Y;
    input  A;
    input  B;
    input  S;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire not_S;
    not not_gate (not_S, S);

    assign Y = (A & not_S) | (B & S);

endmodule