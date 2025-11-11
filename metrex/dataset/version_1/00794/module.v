
module sky130_fd_sc_lp__a32o_4 (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  A3  ,
    input  B1  ,
    input  B2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    sky130_fd_sc_lp__a32o_1 _0_ (
        .X   (X   ),
        .A1  (A1  ),
        .A2  (A2  ),
        .A3  (A3  ),
        .B1  (B1  ),
        .B2  (B2  ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

endmodule
module sky130_fd_sc_lp__a32o_1 (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  A3  ,
    input  B1  ,
    input  B2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    sky130_fd_sc_lp__a31o_1 _0_ (
        .X   (X   ),
        .A1  (A1  ),
        .A2  (A2  ),
        .A3  (A3  ),
        .B1  (B1  ),
        .B2  (B2  ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

endmodule
module sky130_fd_sc_lp__a31o_1 (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  A3  ,
    input  B1  ,
    input  B2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);
    wire s1a,s1b,s2a,s2b;
    sky130_fd_sc_lp__a21o_1 _0_ (
        .X   (s1a),
        .A1  (A1  ),
        .A2  (A2  ),
        .B1  (B1  ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

    sky130_fd_sc_lp__a21o_1 _1_ (
        .X   (s1b),
        .A1  (A3  ),
        .A2  (B2  ),
        .B1  (s1a),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

    sky130_fd_sc_lp__a21o_1 _2_ (
        .X   (s2a),
        .A1  (A1  ),
        .A2  (A2  ),
        .B1  (B2  ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

    sky130_fd_sc_lp__a21o_1 _3_ (
        .X   (s2b),
        .A1  (A3  ),
        .A2  (B1  ),
        .B1  (s2a),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );

    sky130_fd_sc_lp__or2_1 _4_ (
        .X   (X  ),
        .A1  (s1b ),
        .A2  (s2b ),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB ),
        .VNB(VNB )
    );
endmodule
module sky130_fd_sc_lp__a21o_1 (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  B1  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    assign X   = A1 ^ (A2 & B1);

endmodule
module sky130_fd_sc_lp__or2_1 (
    output X   ,
    input  A1  ,
    input  A2  ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    assign X   = A1 | A2;

endmodule