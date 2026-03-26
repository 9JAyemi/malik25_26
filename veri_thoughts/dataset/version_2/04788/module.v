
module sky130_fd_sc_lp__o31ai (
    Y,
    VGND,
    VPB,
    VNB,
    A1,
    A2,
    A3,
    B1
);

    // Module ports
    output Y;
    input VGND;
    input VPB;
    input VNB;
    input A1;
    input A2;
    input A3;
    input B1;

    // Local signals
    wire or0_out;
    wire nand0_out;

    // Name, Output, Other arguments
    or or0 (or0_out, A2, A1, A3);
    nand nand0 (nand0_out, B1, or0_out);
    buf buf0 (Y, nand0_out);

endmodule