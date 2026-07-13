
module my_or_gate (
    input A,
    input B,
    input C_N,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);
    wire A_N, B_N, C;
    nand (A_N, A, B);
    nand (B_N, B, C_N);
    nand (C, A_N, B_N);
    buf (X, C);
endmodule