
module sky130_fd_sc_hd__o21oi (
    X,
    A1,
    A2,
    B1,
    VPB,
    VNB
);

    output X;
    input A1;
    input A2;
    input B1;
    input VPB;
    input VNB;

    assign X = (A1 & A2) | B1;

endmodule

module my_module (
    X   ,
    A1  ,
    A2  ,
    A3  ,
    B1  ,
    B2  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  A3  ;
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    sky130_fd_sc_hd__o21oi base (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(A3),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule
