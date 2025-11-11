


module sky130_fd_sc_lp__a32oi (
    Y ,
    A1,
    A2,
    A3,
    B1,
    B2
);

    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  B2;

    wire nand0_out ;
    wire nand1_out ;
    wire and0_out_Y;

    nand nand0 (nand0_out , A2, A1, A3          );
    nand nand1 (nand1_out , B2, B1              );
    and  and0  (and0_out_Y, nand0_out, nand1_out);
    buf  buf0  (Y         , and0_out_Y          );

endmodule
