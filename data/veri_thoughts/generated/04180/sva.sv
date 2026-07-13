module arduino_switch_digital_uart_bit_sva (
    input logic clk,
    input logic gpio_sel,
    input logic tri_i_out,
    input logic tri_o_out,
    input logic tri_t_out,
    input logic tri_i_in,
    input logic tri_o_in,
    input logic tri_t_in,
    input logic rx_i_in,
    input logic tx_o_in,
    input logic tx_t_in
);

    // RTL is combinational with no reset; clk is only used to sample assertions.

    // tri_o_out selects tri_o_in when gpio_sel is low.
    check_tri_o_gpio_path: assert property (
        @(posedge clk) (gpio_sel === 1'b0) |-> (tri_o_out === tri_o_in)
    );

    // tri_o_out selects tx_o_in when gpio_sel is high.
    check_tri_o_uart_path: assert property (
        @(posedge clk) (gpio_sel === 1'b1) |-> (tri_o_out === tx_o_in)
    );

    // tri_t_out selects tri_t_in when gpio_sel is low.
    check_tri_t_gpio_path: assert property (
        @(posedge clk) (gpio_sel === 1'b0) |-> (tri_t_out === tri_t_in)
    );

    // tri_t_out selects tx_t_in when gpio_sel is high.
    check_tri_t_uart_path: assert property (
        @(posedge clk) (gpio_sel === 1'b1) |-> (tri_t_out === tx_t_in)
    );

    // GPIO mode routes tri_i_out to tri_i_in and clears rx_i_in.
    check_input_demux_gpio_mode: assert property (
        @(posedge clk) (gpio_sel === 1'b0) |-> ((tri_i_in === tri_i_out) && (rx_i_in === 1'b0))
    );

    // UART mode routes tri_i_out to rx_i_in and clears tri_i_in.
    check_input_demux_uart_mode: assert property (
        @(posedge clk) (gpio_sel === 1'b1) |-> ((tri_i_in === 1'b0) && (rx_i_in === tri_i_out))
    );

endmodule