module shift_register_sva (
    input logic       clk,
    input logic       load,
    input logic       shift,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // Load captures data_in when shift is low.
    check_load_without_shift: assert property (
        @(posedge clk) disable iff ($initstate)
        (load && !shift) |=> (data_out == $past(data_in))
    );

    // Shift lefts the register and inserts 0 when load is low.
    check_shift_updates_output: assert property (
        @(posedge clk) disable iff ($initstate)
        (!load && shift) |=> (data_out == {$past(data_out[2:0]), 1'b0})
    );

    // Idle cycles hold the previous register value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        (!load && !shift) |=> (data_out == $past(data_out))
    );

    // Load has priority over shift when both are asserted.
    check_load_priority_over_shift: assert property (
        @(posedge clk) disable iff ($initstate)
        (load && shift) |=> (data_out == $past(data_in))
    );

    // A shift operation always clears the LSB.
    check_shift_clears_lsb: assert property (
        @(posedge clk) disable iff ($initstate)
        (!load && shift) |=> (data_out[0] == 1'b0)
    );

    // A shift operation moves the lower bits into the upper positions.
    check_shift_moves_upper_bits: assert property (
        @(posedge clk) disable iff ($initstate)
        (!load && shift) |=> (data_out[3:1] == $past(data_out[2:0]))
    );

endmodule