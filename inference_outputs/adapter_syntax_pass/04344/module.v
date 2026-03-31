module digital_circuit (
    output Y   ,
    input  A1  ,
    input  A2  ,
    input  B1_N,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    wire base_Y;
    
    assign Y = ((A1 & A2) | (VPWR & !VGND & !A1 & A2) | (!VPWR & VGND & A1 & !A2)) & !B1_N & !(VGND & VPB & VNB);
    
    //sky130_fd_sc_ms__o21bai base (
    //    .Y(base_Y),
    //    .A1(A1),
    //    .A2(A2),
    //    .B1_N(B1_N),
    //    .VPWR(VPWR),
    //    .VGND(VGND),
    //    .VPB(VPB),
    //    .VNB(VNB)
    //);
    
endmodule