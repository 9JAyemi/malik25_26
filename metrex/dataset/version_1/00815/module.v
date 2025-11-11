module sky130_fd_sc_hs__o311ai (
    output Y,
    input A1,
    input A2,
    input A3,
    input B1,
    input C1,
    input VPWR,
    input VGND
);

    // Local signals
    wire B1_or0_out;
    wire nand0_out_Y;
    wire u_vpwr_vgnd0_out_Y;

    // OR gate for A1, A2, and A3
    or or0 (
        B1_or0_out, A1, A2, A3
    );

    // NAND gate for C1, B1, and OR gate output
    nand nand0 (
        nand0_out_Y, C1, B1_or0_out, B1
    );

    // Sky130_fd_sc_hs__u_vpwr_vgnd module
    // sky130_fd_sc_hs__u_vpwr_vgnd u_vpwr_vgnd0 (
    //     u_vpwr_vgnd0_out_Y, nand0_out_Y, VPWR, VGND
    // );

    // Buffer for u_vpwr_vgnd0_out_Y to Y
    buf buf0 (
        Y, nand0_out_Y
    );

endmodule