module shift_register_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] parallel_load,
    input logic        load,
    input logic        shift_left,
    input logic        shift_right,
    input logic [15:0] q,
    input logic        serial_out
);

    // Reset drives both state elements low.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        reset |-> (q == 16'b0) && (serial_out == 1'b0)
    );

    // Load captures parallel_load and reports the previous MSB.
    check_load_updates_register: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (q == $past(parallel_load)) && (serial_out == $past(q[15]))
    );

    // Shift-left moves q left with zero fill and reports the previous MSB.
    check_shift_left_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!load && shift_left) |=> (q == {$past(q[14:0]), 1'b0}) && (serial_out == $past(q[15]))
    );

    // Shift-right moves q right with zero fill and reports the previous LSB.
    check_shift_right_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift_left && shift_right) |=> (q == {1'b0, $past(q[15:1])}) && (serial_out == $past(q[0]))
    );

    // With no command, q holds its value and serial_out reflects the held MSB.
    check_idle_holds_register: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !shift_left && !shift_right) |=> (q == $past(q)) && (serial_out == $past(q[15]))
    );

    // Load has priority over either shift request.
    check_load_priority_over_shifts: assert property (
        @(posedge clk) disable iff (reset)
        (load && (shift_left || shift_right)) |=> (q == $past(parallel_load)) && (serial_out == $past(q[15]))
    );

    // Shift-left has priority over shift-right when load is low.
    check_shift_left_priority_over_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        (!load && shift_left && shift_right) |=> (q == {$past(q[14:0]), 1'b0}) && (serial_out == $past(q[15]))
    );

endmodule