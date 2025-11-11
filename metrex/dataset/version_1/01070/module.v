
module nand4_pwrgood (
    Y,
    A,
    B,
    C,
    VDD,
    VSS
);

    // Module ports
    output  Y   ;
    input   A   ;
    input   B   ;
    input   C   ;
    input   VDD ;
    input   VSS ;

    // Local signals
    wire nand0_out_Y      ;
    wire nand1_out_Y      ;
    wire nand2_out_Y      ;

    //                                 Name         Output             Other arguments
    nand                               nand0       (nand0_out_Y      , B, A, C                );
    nand                               nand1       (nand1_out_Y      , nand0_out_Y, nand0_out_Y);
    nand                               nand2       (nand2_out_Y      , nand1_out_Y, nand1_out_Y);
    not                                inv0         (Y                , nand2_out_Y);

endmodule
