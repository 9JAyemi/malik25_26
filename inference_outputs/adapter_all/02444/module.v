
module my_buffer (
    input  A   ,
    output Z   ,
    input  TE_B,
    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);
 assign Z = TE_B ? A : 1'b0;
endmodule