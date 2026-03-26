
module my_module (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  B1  ,
    input  B2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    wire or0_out;
    wire or1_out;
    wire and0_out_X;

    or or0 (or0_out, A2, A1);
    or or1 (or1_out, B2, B1);
    and and0 (and0_out_X, or0_out, or1_out);
    assign X = and0_out_X & VPWR & ~VGND;
    
endmodule