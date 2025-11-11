module sky130_fd_sc_hd__fahcon (
    input A,
    input B,
    input CI,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output COUT_N,
    output SUM
);

wire w1, w2, w3;

assign w1 = A ^ B;
assign SUM = w1 ^ CI;
assign w2 = A & B;
assign w3 = CI & w1;
assign COUT_N = w2 | w3;

endmodule