


module sky130_fd_sc_ls__einvn (
    Z   ,
    A   ,
    TE_B
);

    output Z   ;
    input  A   ;
    input  TE_B;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    notif0 notif00 (Z     , A, TE_B        );

endmodule
