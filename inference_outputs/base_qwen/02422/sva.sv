module sky130_fd_sc_hdll__nand4bb_sva (
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);
    // NAND operation: Y = D NAND C
    nand_operation: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == !(D & C))
    );

    // OR operation: Y = B_N OR A_N OR (D NAND C)
    or_operation: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == (B_N | A_N | !(D & C)))
    );

    // Buffer operation: Y = B_N OR A_N OR (D NAND C)
    buffer_operation: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == (B_N | A_N | !(D & C)))
    );
endmodule