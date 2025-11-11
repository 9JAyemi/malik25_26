


module sky130_fd_sc_hdll__a21oi (
    Y ,
    A1,
    A2,
    B1
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out  ;
    wire nor0_out_Y;

    and and0 (and0_out  , A1, A2         );
    nor nor0 (nor0_out_Y, B1, and0_out   );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
