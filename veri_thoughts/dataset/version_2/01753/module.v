module my_or4bb (
    input A,
    input B,
    input C_N,
    input D_N,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    // Local signals
    wire nand_out;
    wire or_out;
    wire pwrgood_out;

    // Implementing the NAND gate
    nand nand_gate (nand_out, C_N, D_N);

    // Implementing the OR gate
    or or_gate (or_out, A, B, nand_out);

    // Implementing the power good signal
    assign pwrgood_out = (VPWR > VPB) && (VNB > VGND);

    // Implementing the buffer for X output
    bufif1 output_buf (X, pwrgood_out, or_out);

endmodule