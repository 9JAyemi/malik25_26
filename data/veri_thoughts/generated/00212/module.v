
module my_and4 (
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

    wire A_int, B_int, C_int, D_int, X_int;

    assign A_int = (VPB == 1'b1) ? ~A : A;
    assign B_int = (VPB == 1'b1) ? ~B : B;
    assign C_int = (VPB == 1'b1) ? ~C : C;
    assign D_int = (VPB == 1'b1) ? ~D : D;

    assign X_int = A_int & B_int & C_int & D_int;

    assign X = (VPB == 1'b1) ? ~X_int : X_int;

endmodule