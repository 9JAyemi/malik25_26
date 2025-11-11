


module sky130_fd_sc_ms__ha (
    COUT,
    SUM ,
    A   ,
    B
);

    output COUT;
    output SUM ;
    input  A   ;
    input  B   ;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire and0_out_COUT;
    wire xor0_out_SUM ;

    and and0 (and0_out_COUT, A, B           );
    buf buf0 (COUT         , and0_out_COUT  );
    xor xor0 (xor0_out_SUM , B, A           );
    buf buf1 (SUM          , xor0_out_SUM   );

endmodule
