module my_module (
    output Y   ,
    input  A1_N,
    input  A2_N,
    input  B1  ,
    input  B2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    wire base_Y;

    assign Y = ((A1_N & ~A2_N) & B1) | ((~A1_N & A2_N) & B2) | ((~A1_N & ~A2_N) & 1'b0) | ((A1_N & A2_N) & 1'b1);

endmodule