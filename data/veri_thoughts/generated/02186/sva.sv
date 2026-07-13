module Uart_tx_sva (
    input logic         clk,
    input logic         rst_n,
    input logic [3:0]   num,
    input logic         sel_data,
    input logic [7:0]   rx_data,
    input logic         rs232_tx
);
    // During reset, rs232_tx is driven HIGH.
    reset_value: assert property (
        @(posedge clk) !rst_n |-> (rs232_tx == 1'b1)
    );

    // If last cycle sel_data and num==0, drive start bit LOW.
    update_start_bit_num0: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd0)) |-> (rs232_tx == 1'b0)
    );

    // If last cycle sel_data and num==1, drive rx_data[0].
    update_data_bit0_num1: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd1)) |-> (rs232_tx == $past(rx_data[0]))
    );

    // If last cycle sel_data and num==2, drive rx_data[1].
    update_data_bit1_num2: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd2)) |-> (rs232_tx == $past(rx_data[1]))
    );

    // If last cycle sel_data and num==3, drive rx_data[2].
    update_data_bit2_num3: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd3)) |-> (rs232_tx == $past(rx_data[2]))
    );

    // If last cycle sel_data and num==4, drive rx_data[3].
    update_data_bit3_num4: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd4)) |-> (rs232_tx == $past(rx_data[3]))
    );

    // If last cycle sel_data and num==5, drive rx_data[4].
    update_data_bit4_num5: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd5)) |-> (rs232_tx == $past(rx_data[4]))
    );

    // If last cycle sel_data and num==6, drive rx_data[5].
    update_data_bit5_num6: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd6)) |-> (rs232_tx == $past(rx_data[5]))
    );

    // If last cycle sel_data and num==7, drive rx_data[6].
    update_data_bit6_num7: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd7)) |-> (rs232_tx == $past(rx_data[6]))
    );

    // If last cycle sel_data and num==8, drive rx_data[7].
    update_data_bit7_num8: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd8)) |-> (rs232_tx == $past(rx_data[7]))
    );

    // If last cycle sel_data and num==9, drive stop bit HIGH.
    update_stop_bit_num9: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) == 4'd9)) |-> (rs232_tx == 1'b1)
    );

    // If last cycle sel_data and num>=10 (default), drive HIGH.
    update_default_high_num_ge_10: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(sel_data) && ($past(num) >= 4'd10)) |-> (rs232_tx == 1'b1)
    );

    // If last cycle sel_data was LOW, hold previous value.
    hold_when_sel_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && !$past(sel_data)) |-> (rs232_tx == $past(rs232_tx))
    );
endmodule