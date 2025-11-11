module d_flip_flop_nand (
    input clk,
    input d,
    output q
);

    wire n_clk;
    wire n_d;
    wire n_q;

    assign n_clk = ~clk;
    assign n_d = ~d;

    nand gate1 (n_q, n_d, n_clk);
    nand gate2 (q, n_q, n_clk);

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

    wire [7:0] q_temp;

    d_flip_flop_nand ff0 (clk, d[0], q_temp[0]);
    d_flip_flop_nand ff1 (clk, d[1], q_temp[1]);
    d_flip_flop_nand ff2 (clk, d[2], q_temp[2]);
    d_flip_flop_nand ff3 (clk, d[3], q_temp[3]);
    d_flip_flop_nand ff4 (clk, d[4], q_temp[4]);
    d_flip_flop_nand ff5 (clk, d[5], q_temp[5]);
    d_flip_flop_nand ff6 (clk, d[6], q_temp[6]);
    d_flip_flop_nand ff7 (clk, d[7], q_temp[7]);

    assign q = q_temp;

endmodule