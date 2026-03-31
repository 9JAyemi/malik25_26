module my_module (
    Y ,
    A1,
    A2,
    B1,
    B2
);

    // Module ports
    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;

    // Local signals
    wire nand0_out ;
    wire nand1_out ;
    wire and0_out_Y;
    wire and1_out_Y;

    // Implementing the required logic
    nand nand0 (nand0_out , A2, A1              );
    nand nand1 (nand1_out , B2, B1              );
    and  and0  (and0_out_Y, nand0_out, nand1_out);
    not  not0  (and1_out_Y, and0_out_Y          );
    buf  buf0  (Y         , and1_out_Y          );

endmodule