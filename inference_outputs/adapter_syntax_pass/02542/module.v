module sky130_fd_sc_hs__nand2b (
    input A_N,
    input B,
    input VPWR,
    input VGND,
    output Y
);

    assign Y = ~(A_N & B);

endmodule