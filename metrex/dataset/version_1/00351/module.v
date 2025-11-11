


module sky130_fd_sc_hdll__a21boi (
    Y   ,
    A1  ,
    A2  ,
    B1_N
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire b         ;
    wire and0_out  ;
    wire nor0_out_Y;

    not not0 (b         , B1_N           );
    and and0 (and0_out  , A1, A2         );
    nor nor0 (nor0_out_Y, b, and0_out    );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
