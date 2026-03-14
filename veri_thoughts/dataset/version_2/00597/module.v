
module sky130_fd_sc_ms__a311oi (
    Y,
    A1,
    A2,
    A3,
    B1,
    C1,
    VPWR,
    VGND,
    VPB,
    VNB
);

    output Y;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  C1;
    input  VPWR;
    input  VGND;
    input  VPB;
    input  VNB;

    wire a_and;
    wire b_or_c;

    assign a_and = A1 & A2 & A3;
    assign b_or_c = B1 | C1;

    assign Y = a_and & b_or_c;

endmodule

module my_module (
    Y   ,
    A1  ,
    A2  ,
    A3  ,
    B1  ,
    C1  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  A3  ;
    input  B1  ;
    input  C1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    wire a_and;
    wire b_or_c;

    assign a_and = A1 & A2 & A3;
    assign b_or_c = B1 | C1;

    sky130_fd_sc_ms__a311oi base (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .A3(A3),
        .B1(B1),
        .C1(C1),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
endmodule
