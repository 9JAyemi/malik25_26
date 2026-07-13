module sky130_fd_sc_hs__a21bo (
    output X,
    input A1,
    input A2,
    input B1_N,
    input VPWR,
    input VGND
);

    // Local signals
    wire nand0_out;
    wire nand1_out_X;
    wire u_vpwr_vgnd0_out_X;

    // Instantiate a NAND gate
    nand nand0 (nand0_out, A2, A1);

    // Instantiate another NAND gate
    nand nand1 (nand1_out_X, B1_N, nand0_out);

    // Instantiate a buffer to output the result
    buf buf0 (X, nand1_out_X);

endmodule