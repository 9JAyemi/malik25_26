module INBUF_LVDS_MCCC( 
    PADP, 
    PADN, 
    Y );




    input  PADP;
    input  PADN;
    output Y;

parameter ACT_PIN    = "";

    assign Y = PADP ^ PADN;

endmodule