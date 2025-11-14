
module sky130_fd_sc_hs__nand4bb (
    Y,
    A_N,
    B_N,
    C,
    D
);

    output Y;
    input A_N;
    input B_N;
    input C;
    input D;

    assign Y = ~(A_N & B_N & C & D);

endmodule
