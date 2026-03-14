module sky130_fd_sc_ls__nor3 (input A, B, C, VPWR, VGND, VPB, VNB, output Y);
    assign Y = ~(A | B | C);
endmodule