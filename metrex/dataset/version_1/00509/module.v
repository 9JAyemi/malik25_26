module circuit_design (
    X   ,
    A1  ,
    A2  ,
    A3  ,
    B1  ,
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
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    assign X = (A1) ? 1'b0 :
               (A2) ? 1'b1 :
               (A3) ? 1'b1 :
                      1'b0 ;

endmodule