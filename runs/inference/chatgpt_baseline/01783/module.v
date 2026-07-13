
module two_bit_adder (
    input X   ,
    input A1_N,
    input A2_N,
    input B1  ,
    input B2  ,
    output OUT   
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    wire X1, X2, X3, X4;

    nand (X1, A1_N, A2_N);
    nand (X2, B1, B2);
    nand (X3, A1_N, B2);
    nand (X4, A2_N, B1);
    nor  (OUT, X1, X2);

endmodule