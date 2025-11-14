module sky130_fd_sc_ms__o211a_4 (
    X   ,
    A1  ,
    A2  ,
    B1  ,
    C1  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  C1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    
    assign X = (A1 & A2 & B1 & C1 & VPWR & !VGND & VPB & !VNB);

endmodule