module counter_4bit_assertions (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] load_value,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears count on the next clock, regardless of load or enable.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // Load updates count with load_value on the next clock when not in reset.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(load_value))
    );

    // Enable increments count by one on the next clock when load is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        (!load && enable) |=> (count == ($past(count) + 4'd1))
    );

    // Count holds its value when neither load nor enable is asserted.
    check_count_holds_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !enable) |=> (count == $past(count))
    );

    // Load has priority over enable when both are asserted together.
    check_load_has_priority_over_enable: assert property (
        @(posedge clk) disable iff (reset)
        (load && enable) |=> (count == $past(load_value))
    );

    // A 4-bit increment wraps from 15 back to 0.
    check_enable_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (!load && enable && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule