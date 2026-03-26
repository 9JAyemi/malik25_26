module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

    // Reset clears the counter on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // Reset has priority over load.
    check_reset_overrides_load: assert property (
        @(posedge clk) (reset && load) |=> (count == 4'b0000)
    );

    // A load updates the counter with data_in.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (count == $past(data_in))
    );

    // Without load, the counter increments by one.
    check_increment_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (count == ($past(count) + 4'b0001))
    );

    // The counter wraps from 15 back to 0.
    check_wraparound_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Every non-reset cycle follows the load-or-increment next-state rule.
    check_exact_nonreset_transition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == ($past(load) ? $past(data_in) : ($past(count) + 4'b0001)))
    );

endmodule