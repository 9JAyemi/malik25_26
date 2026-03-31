```systemverilog
module sky130_fd_sc_hdll__nand4bb_sva (
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);
    // NAND operation between D and C
    nand_operation: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == !(D & C))
    ) else $error("NAND operation between D and C is incorrect");

    // OR operation between B_N, A_N, and NAND0_out
    or_operation: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == !(B_N | A_N | !(D & C)))
    ) else $error("OR operation between B_N, A_N, and NAND0_out is incorrect");

    // Buffer operation
    buffer_operation: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == !(B_N | A_N | !(D & C)))
    ) else $error("Buffer operation is incorrect");
endmodule
```