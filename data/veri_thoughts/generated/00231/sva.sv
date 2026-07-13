module shift_register_sva (
    input logic       clk,
    input logic       reset,
    input logic       shift_in,
    input logic       shift,
    input logic [7:0] data_out
);

    // Sampling reset high clears the register by the next clock sample.
    check_reset_clears_data_out: assert property (
        @(posedge clk) reset |=> (data_out == 8'b0)
    );

    // With shift high, the next value shifts in a zero at bit 0.
    check_shift_mode_updates_full_register: assert property (
        @(posedge clk) disable iff (reset)
        shift |=> (data_out == { $past(data_out[6:0]), 1'b0 })
    );

    // With shift low, the next value shifts in shift_in at bit 0.
    check_load_mode_updates_full_register: assert property (
        @(posedge clk) disable iff (reset)
        !shift |=> (data_out == { $past(data_out[6:0]), $past(shift_in) })
    );

    // Upper bits always come from the previous lower bits.
    check_upper_bits_always_shift: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (data_out[7:1] == $past(data_out[6:0]))
    );

    // In shift mode, the next LSB is always zero.
    check_shift_mode_inserts_zero: assert property (
        @(posedge clk) disable iff (reset)
        shift |=> (data_out[0] == 1'b0)
    );

    // In non-shift mode, the next LSB captures shift_in.
    check_load_mode_captures_shift_in: assert property (
        @(posedge clk) disable iff (reset)
        !shift |=> (data_out[0] == $past(shift_in))
    );

endmodule