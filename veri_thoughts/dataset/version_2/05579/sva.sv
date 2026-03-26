module ClockInverter_sva (
    input logic CLK_IN,
    input logic PREEDGE,
    input logic CLK_OUT
);

    // On rising-edge samples of CLK_IN, CLK_OUT matches the inversion of CLK_IN.
    check_clk_out_inverts_on_posedge: assert property (
        @(posedge CLK_IN) (CLK_OUT == !CLK_IN)
    );

    // On falling-edge samples of CLK_IN, CLK_OUT matches the inversion of CLK_IN.
    check_clk_out_inverts_on_negedge: assert property (
        @(negedge CLK_IN) (CLK_OUT == !CLK_IN)
    );

    // On rising-edge samples of CLK_IN, PREEDGE is driven high.
    check_preedge_high_on_posedge: assert property (
        @(posedge CLK_IN) (PREEDGE == 1'b1)
    );

    // On falling-edge samples of CLK_IN, PREEDGE is driven high.
    check_preedge_high_on_negedge: assert property (
        @(negedge CLK_IN) (PREEDGE == 1'b1)
    );

endmodule