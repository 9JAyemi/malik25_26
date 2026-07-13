module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    // NAND0 output is the NAND of A2_N and A1_N
    nand0_output: assert property (
        @(posedge clk) disable iff (!reset_n) (nand0_out == !(A2_N & A1_N))
    );

    // OR0 output is the OR of B2 and B1
    or0_output: assert property (
        @(posedge clk) disable iff (!reset_n) (or0_out == (B2 | B1))
    );

    // NAND1 output is the NAND of NAND0_out and OR0_out
    nand1_output: assert property (
        @(posedge clk) disable iff (!reset_n) (nand1_out_Y == !((nand0_out & or0_out)))
    );

    // Y is the buffer of NAND1_out_Y
    y_output: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == nand1_out_Y)
    );

    // At reset, all outputs should be low
    reset: assert property (
        @(posedge clk) !reset_n |-> (Y == 1'b0) && (nand0_out == 1'b0) && (or0_out == 1'b0) && (nand1_out_Y == 1'b0)
    );
endmodule