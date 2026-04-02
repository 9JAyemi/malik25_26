module sky130_fd_sc_hvl__a22oi_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    output logic Y
);
    // NAND0 output is the result of A2 NAND A1
    nand0_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) (nand0_out == !(A2 & A1))
    );

    // NAND1 output is the result of B2 NAND B1
    nand1_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) (nand1_out == !(B2 & B1))
    );

    // AND0 output is the result of NAND0_out AND NAND1_out
    and0_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) (and0_out_Y == (nand0_out & nand1_out))
    );

    // Y is the result of AND0_out_Y passed through a buffer
    y_out_check: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == and0_out_Y)
    );

    // At reset, all outputs should be low
    reset_check: assert property (
        @(posedge clk) !reset_n |-> (Y == 1'b0)
    );
endmodule