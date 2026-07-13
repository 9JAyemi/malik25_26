module logic_operation (
    output Y,
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

    // Implement AND gates
    wire AB;
    wire CD;
    and (AB, A, B);
    and (CD, C, D);

    // Implement OR gate
    or (Y, AB, CD);

endmodule