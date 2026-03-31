module shift_register_sva (
    input logic       clk,
    input logic       reset,
    input logic       parallel_load,
    input logic       shift_left,
    input logic       shift_right,
    input logic [3:0] parallel_input,
    input logic [3:0] q
);

    // Reset drives q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (q == 4'b0000)
    );

    // Parallel load updates q with the input value.
    check_parallel_load_updates_q: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && $past(parallel_load) |-> (q == $past(parallel_input))
    );

    // Shift-left moves bits left and inserts zero in bit 0.
    check_shift_left_updates_q: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && !$past(parallel_load) && $past(shift_left) |->
            (q == {$past(q[2]), $past(q[1]), $past(q[0]), 1'b0})
    );

    // Shift-right moves bits right and inserts zero in bit 3.
    check_shift_right_updates_q: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && !$past(parallel_load) && !$past(shift_left) && $past(shift_right) |->
            (q == {1'b0, $past(q[3]), $past(q[2]), $past(q[1])})
    );

    // q holds its value when no operation is requested.
    check_idle_holds_q: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && !$past(parallel_load) && !$past(shift_left) && !$past(shift_right) |->
            (q == $past(q))
    );

    // Parallel load has priority over shift requests.
    check_parallel_load_priority_over_shifts: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && $past(parallel_load) && ($past(shift_left) || $past(shift_right)) |->
            (q == $past(parallel_input))
    );

    // Shift-left has priority over shift-right when load is low.
    check_shift_left_priority_over_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) && !$past(parallel_load) && $past(shift_left) && $past(shift_right) |->
            (q == {$past(q[2]), $past(q[1]), $past(q[0]), 1'b0})
    );

    // Reset has priority over load and shift controls.
    check_reset_priority_over_controls: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) && ($past(parallel_load) || $past(shift_left) || $past(shift_right)) |->
            (q == 4'b0000)
    );

endmodule