```systemverilog
module sky130_fd_sc_ms__nand2b_sva (
    input logic Y,
    input logic A_N,
    input logic B
);
    // NAND2B logic: Y = !(A_N & B)
    // A_N and B are inputs, Y is the output
    // The logic is combinational, but we will use a clocked assertion for consistency

    // Property to check the NAND2B logic
    nand2b_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == !(A_N & B))
    ) else $error("NAND2B logic violation");

endmodule
```