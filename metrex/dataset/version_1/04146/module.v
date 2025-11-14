
module sky130_fd_sc_ls__dlrbp (
    input RESET_B,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output Q,
    output Q_N,
    input GATE
);

    wire D_N;
    wire Q_PRE;
    

    assign D_N = ~D;

    nand (Q_PRE, D_N, RESET_B, GATE);
    nand (Q_N, D, RESET_B, GATE);

    assign Q = Q_PRE;
   

endmodule