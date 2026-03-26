module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] init_value,
    input logic [3:0] count
);

    // Reset loads count from init_value on the next sampled cycle.
    check_reset_load: assert property (
        @(posedge clk) reset |=> count == $past(init_value)
    );

    // Without reset, count increments by one on the next sampled cycle.
    check_increment_when_running: assert property (
        @(posedge clk) !reset |=> count == ($past(count) + 4'd1)
    );

    // After reset is released, count matches the value loaded during reset.
    check_state_after_reset_release: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> count == $past(init_value)
    );

    // In free-running mode, the current count matches the prior count plus one.
    check_state_during_free_run: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> count == ($past(count) + 4'd1)
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_f: assert property (
        @(posedge clk) !reset && (count == 4'hF) |=> count == 4'h0
    );

    // Holding reset high across cycles reloads count from init_value each cycle.
    check_held_reset_reloads: assert property (
        @(posedge clk) disable iff ($initstate)
        reset && $past(reset) |-> count == $past(init_value)
    );

endmodule