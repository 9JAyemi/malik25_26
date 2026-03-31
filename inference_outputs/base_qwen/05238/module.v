
module my_or2_8 (
    X   ,
    A   ,
    B   ,
    C   ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    wire or_output;
    or (or_output, A, B);

    assign X = C ? ~or_output : or_output;

endmodule