
module my_module (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    C1  ,
    VPWR,
    VGND
);

    // Module ports
    output Y;
    input  A1;
    input  A2;
    input  B1;
    input  C1;
    input  VPWR;
    input  VGND;

    // Local signals
    wire and0_out         ;
    wire not0_out         ;
    wire or0_out          ;
    wire nor0_out_Y       ;

    // Module instantiations
    and and0 (and0_out, A1, A2);
    not not0 (not0_out, B1);
    or or0 (or0_out, not0_out, C1);
    nor nor0 (nor0_out_Y, and0_out, or0_out);
    buf buf0 (Y, nor0_out_Y);

endmodule