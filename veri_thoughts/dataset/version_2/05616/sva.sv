module shift_register_sva (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Reset clears the register on the following cycle.
    check_reset_clears_output: assert property (
        @(posedge clk)
        reset |=> (data_out == 4'b0000)
    );

    // Reset has priority over load when both are asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk)
        (reset && load) |=> (data_out == 4'b0000)
    );

    // Load captures data_in into the register on the following cycle.
    check_load_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (data_out == $past(data_in))
    );

    // Without load, the register rotates left by one bit.
    check_shift_rotates_left: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (data_out == {$past(data_out[2:0]), $past(data_out[3])})
    );

    // During a shift, the new LSB comes from the previous MSB.
    check_shift_wraps_msb_to_lsb: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (data_out[0] == $past(data_out[3]))
    );

    // Four consecutive shifts restore the previous 4-bit value.
    check_four_shifts_restore_value: assert property (
        @(posedge clk) disable iff (reset)
        (!load ##1 !load ##1 !load ##1 !load) |=> (data_out == $past(data_out, 4))
    );

endmodule