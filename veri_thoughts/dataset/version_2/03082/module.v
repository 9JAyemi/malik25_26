


module sky130_fd_sc_lp__nand2b (
    Y  ,
    A_N,
    B
);

    output Y  ;
    input  A_N;
    input  B  ;

    wire not0_out ;
    wire or0_out_Y;

    not not0 (not0_out , B              );
    or  or0  (or0_out_Y, not0_out, A_N  );
    buf buf0 (Y        , or0_out_Y      );

endmodule
