module sky130_fd_sc_lp__a21oi_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);
    ///// Combinational logic /////
    // Y is the output of a buffer, so it should be equal to the input of the buffer.
    buffer_output: assert property (
        @(posedge CLK) disable iff (!CLK) Y == nor0_out_Y
    );
    // The output of the NOR gate should be the inverse of the AND gate's output.
    nor_output: assert property (
        @(posedge CLK) disable iff (!CLK) nor0_out_Y == ~(and0_out)
    );
    // The AND gate's output should be the logical AND of A1 and A2.
    and_output: assert property (
        @(posedge CLK) disable iff (!CLK) and0_out == (A1 & A2)
    );
    // The input of the NOR gate should be B1 and the AND gate's output.
    nor_input: assert property (
        @(posedge CLK) disable iff (!CLK) nor0_out_Y == ~(B1 & and0_out)
    );
endmodule