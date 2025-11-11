
module four_input_or_gate (
    X   ,
    A   ,
    B   ,
    C   ,
    D   ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  D   ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    wire   AB, CD, ABCD;

    or (AB, A, B);
    or (CD, C, D);
    or (ABCD, AB, CD);

    assign X = ABCD;

endmodule