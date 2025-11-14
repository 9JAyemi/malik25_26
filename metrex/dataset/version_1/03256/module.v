
module nand2 (
    Y,
    A,
    B
);

    // Module ports
    output Y;
    input  A;
    input  B;

    // Local signals
    wire and0_out_Y;
    wire nand0_out_Y;

    //  Name    Output      Other arguments
    nand nand0 (nand0_out_Y, A, B);
    nand nand1 (Y,          nand0_out_Y);

endmodule