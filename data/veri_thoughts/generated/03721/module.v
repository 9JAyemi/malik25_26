
module and2b (
    X   ,
    A   ,
    B   ,
    VPWR,
    VGND
);

    output X   ;
    input  A   ;
    input  B   ;
    input  VPWR;
    input  VGND;
    
    wire A_N;
    nand (A_N, A, 1'b1);

    nand (X, A_N, B);
    
endmodule
