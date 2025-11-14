module sky130_fd_sc_hd__a222oi (
    input  A1  ,
    input  A2  ,
    input  B1  ,
    input  B2  ,
    input  C1  ,
    input  C2  ,
    output Y   ,
    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);

    assign Y = (A1 && !A2) ? 1 :
               (!A1 && A2) ? 0 :
               (!A1 && !A2 && (B1 || C1)) ? 1 :
               (!A1 && !A2 && (B2 || C2)) ? 0 :
               (A1 && A2 && B1 && C1) ? 1 :
               (A1 && A2 && B2 && C2) ? 0 :
               1'b0;

endmodule