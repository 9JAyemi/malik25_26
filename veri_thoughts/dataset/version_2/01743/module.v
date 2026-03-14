module sky130_fd_sc_lp__inputiso1n (
    input A,
    input SLEEP_B,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    assign X = (!A && !SLEEP_B && !VPWR && !VGND && !VPB && !VNB);

endmodule