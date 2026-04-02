module sky130_fd_sc_ls__o32ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // The logic is purely combinational as there are no sequential elements.

    // Check that Y is driven by the OR of the outputs of two NOR gates.
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == (nor1_out | nor0_out))
    );

    // Check that nor0_out is the output of a NOR gate with inputs A3, A1, and A2.
    nor0_output: assert property (
        @(posedge clk) disable iff (!RESETn) (nor0_out == ~(A3 | A1 | A2))
    );

    // Check that nor1_out is the output of a NOR gate with inputs B1 and B2.
    nor1_output: assert property (
        @(posedge clk) disable iff (!RESETn) (nor1_out == ~(B1 | B2))
    );

    // Check that the OR gate's output is the OR of nor1_out and nor0_out.
    or_output: assert property (
        @(posedge clk) disable iff (!RESETn) (or0_out_Y == (nor1_out | nor0_out))
    );

    // Check that the buffer's output is the same as the OR gate's output.
    buffer_output: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == or0_out_Y)
    );
endmodule