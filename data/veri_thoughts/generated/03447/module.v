
module my_module (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  A3  ,
    input  A4  ,
    input  B1  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);
   nand (X, A1, A2, A3);
endmodule