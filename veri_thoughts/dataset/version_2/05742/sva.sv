module pin_control_sva (
    input logic        clk,
    input logic        reset,
    input logic [17:0] data,
    input logic [17:0] out_data
);

    // clk is the only assertion clock.
    // reset is active-high and synchronous.

    // A reset cycle clears the registered output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (out_data == 18'b0)
    );

    // The upper 17 bits shift toward MSB on each active cycle.
    check_shift_upper_bits: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out_data[17:1] == $past(out_data[16:0]))
    );

    // The LSB captures data[0] on each active cycle.
    check_shift_lsb_capture: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out_data[0] == $past(data[0]))
    );

    // Eighteen shifted-in zeros flush the whole register to zero.
    check_zero_stream_flushes_register: assert property (
        @(posedge clk) disable iff (reset)
        (data[0] == 1'b0)[*18] |=> (out_data == 18'b0)
    );

    // Eighteen shifted-in ones fill the whole register with ones.
    check_one_stream_fills_register: assert property (
        @(posedge clk) disable iff (reset)
        (data[0] == 1'b1)[*18] |=> (out_data == 18'h3FFFF)
    );

endmodule