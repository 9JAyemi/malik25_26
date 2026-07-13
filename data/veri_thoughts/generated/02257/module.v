


module sky130_fd_sc_ls__einvp (
    Z ,
    A ,
    TE
);

    output Z ;
    input  A ;
    input  TE;

    notif1 notif10 (Z     , A, TE          );

endmodule
