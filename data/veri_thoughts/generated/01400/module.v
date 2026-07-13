module verilog_module (
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output out
);

    sky130_fd_sc_hvl__fill_8 base (
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB),
        .out(out)
    );

endmodule

module sky130_fd_sc_hvl__fill_8 (
    input VPWR,
    input VGND,
    input VPB ,
    input VNB ,
    output out
);

    assign out = VPWR & VGND & VPB & VNB;

endmodule