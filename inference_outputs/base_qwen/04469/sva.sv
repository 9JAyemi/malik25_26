```systemverilog
module sky130_fd_sc_ls__a32oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // NAND0 output is the result of A2 NAND A1 NAND A3
    nand0_output: assert property (
        @(posedge clk) disable iff (!RESETn) (nand0_out == !(A2 & A1 & A3))
    );

    // NAND1 output is the result of B2 NAND B1
    nand1_output: assert property (
        @(posedge clk) disable iff (!RESETn) (nand1_out == !(B2 & B1))
    );

    // AND0 output is the result of NAND0_out AND NAND1_out
    and0_output: assert property (
        @(posedge clk) disable iff (!RESETn) (and0_out_Y == (nand0_out & nand1_out))
    );

    // Y is the result of AND0_out_Y passed through a buffer
    y_output: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == and0_out_Y)
    );

    // At reset, all outputs should be LOW
    reset: assert property (
        @(posedge clk) !RESETn |-> (Y == 1'b0) && (nand0_out == 1'b0) && (nand1_out == 1'b0) && (and0_out_Y == 1'b0)
    );
endmodule
```