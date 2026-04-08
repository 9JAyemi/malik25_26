module and4 (
    output X,
    input  A,
    input  B,
    input  C,
    input  D
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire temp1, temp2;

    and u1 (temp1, A, B, C);
    and u2 (temp2, temp1, C, D);
    assign X = temp2;

endmodule