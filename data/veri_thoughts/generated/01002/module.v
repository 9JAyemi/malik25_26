
module full_adder (
    input A,
    input B,
    input CI,
    output SUM,
    output COUT_N
);

    wire xor0_out_SUM;
    wire a_b;
    wire a_ci;
    wire b_ci;
    wire or0_out_coutn;

    xor xor0 (xor0_out_SUM, A, B, CI);
    assign SUM = xor0_out_SUM;
    nor nor0 (a_b, A, B);
    nor nor1 (a_ci, A, CI);
    nor nor2 (b_ci, B, CI);
    or or0 (or0_out_coutn, a_b, a_ci, b_ci);
    assign COUT_N = or0_out_coutn;

endmodule
