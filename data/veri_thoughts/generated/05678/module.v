
module module_top (
    X   , A1  , A2  , B1  , C1  , D1  ,
    VPWR, VGND, VPB , VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  C1  ;
    input  D1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    sky130_fd_sc_ls__a2111o_1 base (
        .X  (X  ),
        .A1 (A1 ),
        .A2 (A2 ),
        .B1 (B1 ),
        .C1 (C1 ),
        .D1 (D1 ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB (VPB),
        .VNB (VNB)
    );

endmodule
module sky130_fd_sc_ls__a2111o_1 (
    X   , A1  , A2  , B1  , C1  , D1  ,
    VPWR, VGND, VPB , VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  C1  ;
    input  D1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    wire X;

    assign X = (A1 & A2) | (B1 & C1) | (D1 & VNB);
    
endmodule