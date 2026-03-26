
module sky130_fd_sc_lp__o41a_m (
    X   ,
    A1  ,
    A2  ,
    A3  ,
    A4  ,
    B1  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  A3  ;
    input  A4  ;
    input  B1  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    wire _00_, _01_, _02_, _03_, _04_, _05_, _06_, _07_;

    and (_00_, A1, A2);
    and (_01_, _00_, A4);
    and (X, _01_, B1);
    and (_02_, A3, A4);
    and (_03_, A2, _02_);
    and (_04_, A1, _03_);
    or (_05_, X, _04_);
    and (_06_, X, _05_);
    or (_07_, _05_, _06_);

endmodule
