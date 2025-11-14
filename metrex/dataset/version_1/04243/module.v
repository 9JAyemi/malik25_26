
module nand4 (
    Y   ,
    A   ,
    B   ,
    C   ,
    D   ,
    VPWR,
    VGND
);

    output Y   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  D   ;
    input  VPWR;
    input  VGND;

    wire nand1_out;
    wire nand2_out;
    wire nand3_out;

    nand (nand1_out, A, B);
    nand (nand2_out, C, D);
    nand (nand3_out, nand1_out, nand2_out);
    nand (Y, nand3_out, nand3_out);

endmodule