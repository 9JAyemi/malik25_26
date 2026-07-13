module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic parallel_load,
    input logic shift_left,
    input logic shift_right,
    input logic [3:0] parallel_input,
    input logic [3:0] q
);

    // Reset clears the register on the next clock.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // Parallel load captures parallel_input when shift controls are inactive.
    check_parallel_load: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (q == $past(parallel_input))
    );

    // Shift left moves bits [2:0] into [3:1] and inserts 0 in bit [0].
    check_shift_left: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && shift_left) |=> (q == {$past(q[2:0]), 1'b0})
    );

    // Shift right moves bits [3:1] into [2:0] and inserts 0 in bit [3].
    check_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && !shift_left && shift_right) |=> (q == {1'b0, $past(q[3:1])})
    );

    // The register holds its value when no control is active.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && !shift_left && !shift_right) |=> (q == $past(q))
    );

    // Parallel load has priority over shift_left.
    check_parallel_load_priority: assert property (
        @(posedge clk) disable iff (reset)
        (parallel_load && shift_left) |=> (q == $past(parallel_input))
    );

    // Parallel load has priority over shift_right.
    check_parallel_load_priority_over_shift_right: assert property (
        @(posedge clk) disable iff (reset)
        (parallel_load && !shift_left && shift_right) |=> (q == $past(parallel_input))
    );

endmodule