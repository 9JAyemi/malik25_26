
module and_module (
    output X   ,
    input  A_N ,
    input  B_N ,
    input  C   ,
    input  D   ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    wire AB, CD, ABCD;
    and (AB, A_N, B_N);
    and (CD, C, D);
    and (ABCD, AB, CD);
    assign X = ABCD;

endmodule
