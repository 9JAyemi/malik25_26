module counter_4bit_sync_reset_load_sva (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] count
);

    // Count follows the prior cycle's reset, load, then increment priority.
    check_next_state_function: assert property (
        @(posedge clk) disable iff ($initstate)
        count == ($past(reset) ? 4'b0000 :
                  ($past(load)  ? $past(data_in) :
                                  ($past(count) + 4'd1)))
    );

    // A sampled reset clears the counter on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'b0000)
    );

    // Reset overrides load when both are sampled high.
    check_reset_overrides_load: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset && load) |-> (count == 4'b0000)
    );

    // A sampled load updates count with the sampled input data.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(!reset && load) |-> (count == $past(data_in))
    );

    // Without reset or load, the counter increments by one.
    check_increment_when_idle: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(!reset && !load) |-> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 to 0 when incrementing.
    check_wraparound_on_overflow: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(!reset && !load && (count == 4'hF)) |-> (count == 4'h0)
    );

endmodule