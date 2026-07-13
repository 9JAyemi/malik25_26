
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

    // Module ports

    // Local signals
    wire b                ;
    wire and0_out         ;
    wire nor0_out_Y       ;
    wire pwrgood_pp0_out_Y;

    // Components instantiation
    not not0 (b, B1_N);
    and and0 (and0_out, A1, A2);
    nor nor0 (nor0_out_Y, b, and0_out);
    buf buf0 (pwrgood_pp0_out_Y, nor0_out_Y);
    buf buf1 (Y, pwrgood_pp0_out_Y);  // Fixing the issue

endmodule