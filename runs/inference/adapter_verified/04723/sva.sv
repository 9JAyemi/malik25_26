module top_module_sva (
    input logic clk,
    input logic areset,
    input logic load,
    input logic ena,
    input logic [3:0] data,
    input logic [3:0] q
);

// Reset clears q on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) areset |=> (q == 4'b0000)
    );

// Load captures data into q when ena is low.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (areset)
        (load && !ena) |=> (q == $past(data))
    );

// Load has priority over ena when both are high.
    check_load_priority_over_ena: assert property (
        @(posedge clk) disable iff (areset)
        (load && ena) |=> (q == $past(data))
    );

// ena shifts q left by one when load is low.
    check_shift_left_when_enabled: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (q == {1'b0, $past(q[3:1])})
    );

// With no control active, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (q == $past(q))
    );

endmodule
