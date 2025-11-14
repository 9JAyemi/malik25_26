


module sky130_fd_sc_hvl__einvp (
    Z ,
    A ,
    TE
);

    output Z ;
    input  A ;
    input  TE;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    notif1 notif10 (Z     , A, TE          );

endmodule
