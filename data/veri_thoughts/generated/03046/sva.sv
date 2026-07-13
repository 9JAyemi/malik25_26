module EtherCAT_master_sva (
    input logic       clk,
    input logic       rst,
    input logic [7:0] tx_data,
    input logic       tx_valid,
    input logic [7:0] rx_data,
    input logic       rx_valid,
    input logic       tx_ready,
    input logic       rx_ready
);

    // Reset clears the registered outputs by the next sampled cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (tx_ready == 1'b0) && (rx_data == 8'b0)
    );

    // tx_ready asserts one cycle after both tx_valid and rx_ready are high.
    check_tx_ready_asserts_on_valid_and_ready: assert property (
        @(posedge clk) disable iff (rst) (tx_valid && rx_ready) |=> tx_ready
    );

    // tx_ready deasserts one cycle after either tx_valid or rx_ready is low.
    check_tx_ready_deasserts_without_valid_or_ready: assert property (
        @(posedge clk) disable iff (rst) (!(tx_valid && rx_ready)) |=> !tx_ready
    );

    // rx_data holds its value on every non-reset clock.
    check_rx_data_holds_value: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> $stable(rx_data)
    );

endmodule

module EtherCAT_slave_sva (
    input logic       clk,
    input logic       rst,
    input logic [7:0] tx_data,
    input logic       tx_valid,
    input logic [7:0] rx_data,
    input logic       rx_valid,
    input logic       tx_ready,
    input logic       rx_ready
);

    // Reset clears the transmit registers by the next sampled cycle.
    check_reset_clears_tx_outputs: assert property (
        @(posedge clk) rst |=> (tx_data == 8'b0) && (tx_valid == 1'b0)
    );

    // Reset clears the receive side registers by the next sampled cycle.
    check_reset_clears_rx_outputs: assert property (
        @(posedge clk) rst |=> (rx_ready == 1'b0) && (rx_valid == 1'b0)
    );

    // tx_data holds its value on every non-reset clock.
    check_tx_data_holds_value: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> $stable(tx_data)
    );

    // tx_valid and rx_valid assert one cycle after tx_ready is high.
    check_valid_outputs_assert_on_ready: assert property (
        @(posedge clk) disable iff (rst) tx_ready |=> (tx_valid && rx_valid)
    );

    // tx_valid and rx_valid deassert one cycle after tx_ready is low.
    check_valid_outputs_deassert_without_ready: assert property (
        @(posedge clk) disable iff (rst) !tx_ready |=> (!tx_valid && !rx_valid)
    );

    // rx_ready asserts on every non-reset clock.
    check_rx_ready_asserts_outside_reset: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> rx_ready
    );

endmodule