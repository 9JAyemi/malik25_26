
module sky130_fd_sc_hdll__nand4 (
    Y,
    A,
    B,
    C,
    D
);

    // Module ports
    output Y;
    input  A;
    input  B;
    input  C;
    input  D;

    // Local signals
    wire nand0_out;
    wire nand1_out;
    wire nand2_out;
    wire not0_out;
    wire and0_out;
    wire and1_out;
    wire or0_out;

    //   Name        Output       Other arguments
    nand nand0     (nand0_out,   A, B);
    nand nand1     (nand1_out,   C, D);
    nand nand2     (nand2_out,   nand0_out, nand1_out);
    not  not0      (not0_out,    nand2_out);
    and  and0      (and0_out,    A, B);
    and  and1      (and1_out,    C, D);
    or   or0       (or0_out,     and0_out, and1_out);
    buf  buf0      (Y,           not0_out, or0_out);

endmodule
