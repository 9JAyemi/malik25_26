module nor_and(
    output Y,
    input A, B, C, D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Local signals
    wire nor1_out, nor2_out, nor3_out;

    // NOR gates
    nor nor1(nor1_out, A, B);
    nor nor2(nor2_out, C, D);
    nor nor3(Y, nor1_out, nor2_out);

endmodule