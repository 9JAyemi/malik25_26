module echotest_sva (
    input logic i_clk,
    input logic i_uart_rx,
    input logic o_uart_tx
);

    // TX is the prior sampled value of RX.
    check_registered_echo: assert property (
        @(posedge i_clk) 1'b1 |=> (o_uart_tx == $past(i_uart_rx))
    );

    // An RX rising edge appears on TX one clock later.
    check_rise_propagates: assert property (
        @(posedge i_clk) $rose(i_uart_rx) |=> $rose(o_uart_tx)
    );

    // An RX falling edge appears on TX one clock later.
    check_fall_propagates: assert property (
        @(posedge i_clk) $fell(i_uart_rx) |=> $fell(o_uart_tx)
    );

    // Stable RX across a cycle yields stable TX on the next cycle.
    check_stable_propagates: assert property (
        @(posedge i_clk) $stable(i_uart_rx) |=> $stable(o_uart_tx)
    );

    // Changed RX across a cycle yields changed TX on the next cycle.
    check_change_propagates: assert property (
        @(posedge i_clk) $changed(i_uart_rx) |=> $changed(o_uart_tx)
    );

endmodule