module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic parallel_load,
    input logic shift_left,
    input logic shift_right,
    input logic [3:0] parallel_input,
    input logic [3:0] q
);

    // Reset clears the register on the next cycle.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // Parallel load captures parallel_input when not in reset.
    check_parallel_load_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (q == $past(parallel_input))
    );

    // Shift left moves the register left and inserts 0 into bit 0.
    check_shift_left_moves_register: assert property (
        @(posedge clk) disable iff (reset)
        shift_left |=> (q == {$past(q[2:0]), 1'b0})
    );

    // Shift right moves the register right and inserts 0 into bit 3.
    check_shift_right_moves_register: assert property (
        @(posedge clk) disable iff (reset)
        shift_right |=> (q == {1'b0, $past(q[3:1])})
    );

    // With no active control, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        !parallel_load && !shift_left && !shift_right |=> (q == $past(q))
    );

    // Load has priority over shift_left when both are asserted.
    check_load_priority_over_shift_left: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load && shift_left |=> (q == $past(parallel_input))
    );

    // Load has priority over shift_right when both are asserted.
    check_load_priority_over_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load && shift_right |=> (q == $past(parallel_input))
    );

    // Shift_left has priority over shift_right when both are asserted.
    check_shift_left_priority_over_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        shift_left && shift_right |=> (q == {$past(q[2:0]), 1'b0})
    );

endmodule