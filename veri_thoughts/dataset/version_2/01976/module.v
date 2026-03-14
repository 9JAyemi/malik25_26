
module sky130_fd_sc_lp__a22o_m (
    X   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    sky130_fd_sc_lp__a22o_1 base (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule
module sky130_fd_sc_lp__a22o_1 (
    X    ,
    A1   ,
    A2   ,
    B1   ,
    B2   ,
    VPWR ,
    VGND ,
    VPB  ,
    VNB  
);
    output X    ;
    input  A1   ;
    input  A2   ;
    input  B1   ;
    input  B2   ;
    input  VPWR ;
    input  VGND ;
    input  VPB  ;
    input  VNB  ;
    wire  an_a1   ;
    wire  an_a2   ;
    wire  an_b1   ;
    wire  an_b2   ;
    wire  s_ann12 ;

    sky130_fd_sc_lp__nand2_2 _0_ (
        .A(A1),
        .B(A2),
        .Y(an_a1)
    );
    sky130_fd_sc_lp__nand2_2 _1_ (
        .A(B1),
        .B(B2),
        .Y(an_b1)
    );
    sky130_fd_sc_lp__or2_1 _2_ (
        .A(an_a1),
        .B(an_b1),
        .X(s_ann12)
    );
    sky130_fd_sc_lp__inv_2 _3_ (
        .A(s_ann12),
        .Y(X)
    );
endmodule
module sky130_fd_sc_lp__nand2_2 (
    A    ,
    B    ,
    Y    
);
    input  A    ;
    input  B    ;
    output Y    ;

    nand ( Y ,  A ,  B );

endmodule
module sky130_fd_sc_lp__or2_1 (
    A    ,
    B    ,
    X    
);
    input  A    ;
    input  B    ;
    output X    ;

    or ( X ,  A ,  B );

endmodule
module sky130_fd_sc_lp__inv_2 (
    A    ,
    Y    
);
    input  A    ;
    output Y    ;

    not ( Y ,  A );

endmodule