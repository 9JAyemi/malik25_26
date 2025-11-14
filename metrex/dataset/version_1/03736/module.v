
module my_nor4 (
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
    
    wire n1, n2, n3, n4;

    nor (n1, A, B);
    nor (n2, C, D);
    nor (n3, n1, n2);
    nor (n4, n3, n3);
    nor (Y, n4, n4);

endmodule
