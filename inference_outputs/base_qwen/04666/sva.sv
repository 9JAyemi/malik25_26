```systemverilog
module sky130_fd_sc_hvl__nand2_sva (
    input logic Y,
    input logic A,
    input logic B
);
    // NAND gate output should be the negation of the AND of A and B
    nand_behavior: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == ~(A & B))
    );
endmodule
```