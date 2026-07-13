module shift_register_sva (
    input logic [3:0] data_in,
    input logic       shift,
    input logic       load,
    input logic       clk,
    input logic [3:0] out
);
    // Clock: clk. No reset present. Sequential logic with synchronous load and shift-left.

    // Load drives out to data_in on next cycle.
    load_updates_out: assert property (
        @(posedge clk) load |=> (out == $past(data_in))
    );

    // Load has priority over shift when both are asserted.
    load_has_priority_over_shift: assert property (
        @(posedge clk) (load && shift) |=> (out == $past(data_in))
    );

    // Shift (when load is low) updates out to left-shift with zero fill.
    shift_updates_out_when_no_load: assert property (
        @(posedge clk) (!load && shift) |=> (out == {$past(out[2:0]), 1'b0})
    );

    // When idle (no load, no shift), out holds its value.
    hold_when_no_op: assert property (
        @(posedge clk) (!load && !shift) |=> (out == $past(out))
    );

    // On shift without load, LSB is zero-filled.
    shift_zero_fill_lsb: assert property (
        @(posedge clk) (!load && shift) |=> (out[0] == 1'b0)
    );

    // On shift without load, MSB gets previous bit[2].
    shift_msb_from_prev_bit2: assert property (
        @(posedge clk) (!load && shift) |=> (out[3] == $past(out[2]))
    );

    // On shift without load, bit[2] gets previous bit[1].
    shift_bit2_from_prev_bit1: assert property (
        @(posedge clk) (!load && shift) |=> (out[2] == $past(out[1]))
    );

    // On shift without load, bit[1] gets previous bit[0].
    shift_bit1_from_prev_bit0: assert property (
        @(posedge clk) (!load && shift) |=> (out[1] == $past(out[0]))
    );

    // Two consecutive shifts (with load low) equal a two-bit left shift with zero fill.
    double_left_shift_over_two_cycles: assert property (
        @(posedge clk) (!load && shift) ##1 (!load && shift) |=> (out == { $past(out,2)[1:0], 2'b00 })
    );

endmodule