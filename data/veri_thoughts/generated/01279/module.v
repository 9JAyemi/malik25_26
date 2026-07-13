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

    wire a2_and_a3;
    wire b2_or_vpwr;
    wire vpb_xor_vnb;

    assign a2_and_a3 = A2 & A3;
    assign b2_or_vpwr = B2 | VPWR;
    assign vpb_xor_vnb = VPB ^ VNB;

    assign X = (A1 & a2_and_a3) | (~A1 & B1 & b2_or_vpwr) | (~A1 & ~B1 & vpb_xor_vnb);

endmodule