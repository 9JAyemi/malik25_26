module my_module (
    X   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    // Module ports
    output X   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    // Local signals
    wire nand0_out ;
    wire or0_out   ;
    wire and0_out_X;

    //   Name   Output      Other arguments
    nand nand0 (nand0_out , A2_N, A1_N        );
    or   or0   (or0_out   , B2, B1            );
    and  and0  (and0_out_X, nand0_out, or0_out);
    buf  buf0  (X         , and0_out_X        );

endmodule