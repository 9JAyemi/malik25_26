module memory_decoder_sva (
    input logic [7:0] address,
    input logic [7:0] data_in,
    input logic [7:0] switch_in,
    input logic clk,
    input logic res,
    input logic write_enable,
    input logic [7:0] LED_status,
    input logic [7:0] data_out
);
    // LED_status must be 0 while reset is asserted.
    reset_led_status_zero: assert property (
        @(posedge clk) res |-> (LED_status == 8'h00)
    );

    // While reset is asserted and address==0xFF, data_out (switch path) must be 0.
    reset_switch_path_zero: assert property (
        @(posedge clk) res && (&address) |-> (data_out == 8'h00)
    );

    // Writing to address 0xFF updates LED_status with data_in on the next cycle.
    led_updates_on_we_ffff: assert property (
        @(posedge clk) disable iff (res) (write_enable && (&address)) |=> (LED_status == $past(data_in))
    );

    // LED_status holds when not writing to address 0xFF.
    led_holds_without_enable: assert property (
        @(posedge clk) disable iff (res) (!(write_enable && (&address))) |=> (LED_status == $past(LED_status))
    );

    // Any LED_status change requires a 0xFF write in the prior cycle (outside reset).
    led_change_requires_prev_enable: assert property (
        @(posedge clk) disable iff (res) (LED_status != $past(LED_status)) |-> $past(write_enable && (&address) && !res)
    );

    // When address==0xFF, data_out is the prior-cycle switch_in sample.
    dataout_switch_samples_prev: assert property (
        @(posedge clk) disable iff (res) (&address) |-> (data_out == $past(switch_in))
    );

    // When address!=0xFF and write_enable, data_out reflects data_in in the same cycle.
    dataout_mem_write_same_cycle: assert property (
        @(posedge clk) disable iff (res) ((~&address) && write_enable) |-> (data_out == data_in)
    );

    // If address!=0xFF for two cycles and no writes in either cycle edge, data_out holds.
    dataout_mem_hold_no_write: assert property (
        @(posedge clk) disable iff (res) ((~&address) && (~&$past(address)) && !write_enable && !$past(write_enable)) |-> (data_out == $past(data_out))
    );

    // After a reset cycle, LED_status stays 0 until a 0xFF write occurs.
    led_zero_after_reset_until_write: assert property (
        @(posedge clk) disable iff (res) $past(res) && !(write_enable && (&address)) |-> (LED_status == 8'h00)
    );
endmodule