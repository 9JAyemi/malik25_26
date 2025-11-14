


module sky130_fd_sc_ls__clkdlyinv5sd1 (
    Y,
    A
);

    output Y;
    input  A;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire not0_out_Y;

    not not0 (not0_out_Y, A              );
    buf buf0 (Y         , not0_out_Y     );

endmodule
