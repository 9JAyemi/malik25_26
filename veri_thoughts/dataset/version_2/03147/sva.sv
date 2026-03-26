module init_clk_delay_assertions (
    input logic INIT_CLK,
    input logic INIT_CLK_O
);

    // After any rising edge, the output is high by the next sampled rising edge.
    check_output_high_by_next_edge: assert property (
        @(posedge INIT_CLK)
        1'b1 |=> (INIT_CLK_O === 1'b1)
    );

    // Once the output is observed high, it remains high on later sampled rising edges.
    check_output_stays_high_once_set: assert property (
        @(posedge INIT_CLK)
        (INIT_CLK_O === 1'b1) |=> (INIT_CLK_O === 1'b1)
    );

    // The output cannot show a falling transition across sampled rising edges.
    check_output_never_falls: assert property (
        @(posedge INIT_CLK)
        !$fell(INIT_CLK_O)
    );

endmodule