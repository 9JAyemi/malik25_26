module custom_logic (
    output Y,
    input  A1,
    input  A2,
    input  B1_N
);

    // Local signals
    wire not_B1_N;
    wire and0_out;
    wire and1_out;
    wire or0_out;
    wire nand0_out_Y;

    // Gate-level primitives
    not  u_not_B1_N (not_B1_N, B1_N);
    and  u_and0     (and0_out, A1, A2);
    and  u_and1     (and1_out, not_B1_N, and0_out);
    or   u_or0      (or0_out, A1, A2);
    nand u_nand0    (nand0_out_Y, and1_out, or0_out);
    buf  u_buf0     (Y, nand0_out_Y);

endmodule
