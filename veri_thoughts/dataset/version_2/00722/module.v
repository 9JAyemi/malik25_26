module and_gate (
    X   ,
    A1  ,
    A2  ,
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
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    
    wire and1;
    wire and2;
    wire and3;
    
    assign and1 = A1 & A2;
    assign and2 = B1 & B2;
    assign and3 = and1 & and2;
    
    assign X = and3;
    
endmodule