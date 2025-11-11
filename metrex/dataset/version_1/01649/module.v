module my_module (
    X   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    C1  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    // Module ports
    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  C1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    // Local signals
    wire and0_out         ;
    wire and1_out         ;
    wire or0_out_X        ;
    wire pwrgood_pp0_out_X;

    // Internal modules
    my_and  and0 (and0_out, B1, B2);
    my_and  and1 (and1_out, A1, A2);
    my_or   or0  (or0_out_X, and1_out, and0_out, C1);
    my_pg   pg0  (pwrgood_pp0_out_X, or0_out_X, VPWR, VGND);
    my_buf  buf0 (X, pwrgood_pp0_out_X);

endmodule

module my_and (
    out,
    in1,
    in2
);

    // Module ports
    output out;
    input  in1;
    input  in2;

    // Local signals
    wire and_out;

    // Implementation
    assign and_out = in1 & in2;
    assign out     = and_out;

endmodule

module my_or (
    out,
    in1,
    in2,
    in3
);

    // Module ports
    output out;
    input  in1;
    input  in2;
    input  in3;

    // Local signals
    wire or_out;

    // Implementation
    assign or_out = in1 | in2 | in3;
    assign out    = or_out;

endmodule

module my_pg (
    out,
    in1,
    in2,
    in3
);

    // Module ports
    output out;
    input  in1;
    input  in2;
    input  in3;

    // Local signals
    wire pg_out;

    // Implementation
    assign pg_out = in1 & ~in2 & in3;
    assign out    = pg_out;

endmodule

module my_buf (
    out,
    in1
);

    // Module ports
    output out;
    input  in1;

    // Implementation
    assign out = in1;

endmodule