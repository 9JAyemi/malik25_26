


module sky130_fd_sc_ls__fahcon (
    COUT_N,
    SUM   ,
    A     ,
    B     ,
    CI
);

    output COUT_N;
    output SUM   ;
    input  A     ;
    input  B     ;
    input  CI    ;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire xor0_out_SUM ;
    wire a_b          ;
    wire a_ci         ;
    wire b_ci         ;
    wire or0_out_coutn;

    xor xor0 (xor0_out_SUM , A, B, CI       );
    buf buf0 (SUM          , xor0_out_SUM   );
    nor nor0 (a_b          , A, B           );
    nor nor1 (a_ci         , A, CI          );
    nor nor2 (b_ci         , B, CI          );
    or  or0  (or0_out_coutn, a_b, a_ci, b_ci);
    buf buf1 (COUT_N       , or0_out_coutn  );

endmodule
