module counter_sva (
    input logic        clk,
    input logic        reset,
    input logic        enable,
    input logic        load,
    input logic [31:0] load_value,
    input logic [31:0] count
);

    // Synchronous reset drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 32'd0)
    );

    // Load updates count with load_value on the next cycle.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(load_value))
    );

    // Load has priority over enable when both are asserted.
    check_load_priority_over_enable: assert property (
        @(posedge clk) disable iff (reset)
        (load && enable) |=> (count == $past(load_value))
    );

    // Enable increments count by one when load is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !load) |=> (count == ($past(count) + 32'd1))
    );

    // Count holds its value when no control input is asserted.
    check_idle_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !enable) |=> (count == $past(count))
    );

endmodule