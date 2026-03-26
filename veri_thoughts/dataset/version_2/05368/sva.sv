module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [2:0] load_data,
    input logic serial_out
);

    // After reset is deasserted, the cleared register drives serial_out low.
    check_reset_release_clears_serial: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (serial_out == 1'b0)
    );

    // A load updates serial_out to the loaded LSB on the next cycle.
    check_load_updates_serial_lsb: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (serial_out == $past(load_data[0]))
    );

    // One shift after a load moves the loaded MSB to serial_out.
    check_one_shift_outputs_loaded_msb: assert property (
        @(posedge clk) disable iff (reset)
        (load) ##1 (!load) |=> (serial_out == $past(load_data[2], 2))
    );

    // Two shifts after a load move the loaded middle bit to serial_out.
    check_two_shifts_output_loaded_mid: assert property (
        @(posedge clk) disable iff (reset)
        (load) ##1 (!load) ##1 (!load) |=> (serial_out == $past(load_data[1], 3))
    );

    // Three shifts after a load wrap serial_out back to the loaded LSB.
    check_three_shifts_wrap_to_loaded_lsb: assert property (
        @(posedge clk) disable iff (reset)
        (load) ##1 (!load) ##1 (!load) ##1 (!load) |=> (serial_out == $past(load_data[0], 4))
    );

    // If no load occurs on reset release, the zero state shifts as zero on the next cycle.
    check_zero_state_holds_one_idle_cycle: assert property (
        @(posedge clk) disable iff (reset)
        ($fell(reset) && !load) |=> (serial_out == 1'b0)
    );

    // If no load occurs for two cycles after reset release, serial_out remains low.
    check_zero_state_holds_two_idle_cycles: assert property (
        @(posedge clk) disable iff (reset)
        ($fell(reset) && !load) ##1 (!load) |=> (serial_out == 1'b0)
    );

endmodule