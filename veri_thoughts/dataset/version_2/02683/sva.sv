module binary_counter_sva #(parameter int N = 4) (
    input  logic              clk,
    input  logic              rst,    // active-low async reset
    input  logic [N-1:0]      count
);

    // When reset is asserted low at a clock edge, count is 0.
    reset_forces_zero_now: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == {N{1'b0}})
    );

    // On reset falling edge, count is 0 at that cycle.
    reset_fall_clears_counter: assert property (
        @(posedge clk) $fell(rst) |-> (count == {N{1'b0}})
    );

    // On reset rising edge, counter starts at 1.
    reset_rise_starts_at_one: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == {{(N-1){1'b0}},1'b1})
    );

    // When rst is HIGH in consecutive samples, counter either increments by 1 or equals 1 if reset pulsed low between edges.
    increment_or_one_when_running: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> ((count == $past(count) + 1'b1) || (count == {{(N-1){1'b0}},1'b1}))
    );

    // While held in reset across consecutive samples, count stays at 0.
    count_stable_in_reset: assert property (
        @(posedge clk) ($past(rst) == 1'b0 && rst == 1'b0) |-> (count == {N{1'b0}} && $past(count) == {N{1'b0}})
    );

    // If running and counter reads 0, previous sample was all 1's (wrap-around).
    wraparound_implies_prev_all_ones: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && (count == {N{1'b0}})) |-> ($past(count) == {N{1'b1}})
    );

    // On reset rising edge, the previous sampled count was 0.
    reset_rise_prev_count_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> ($past(count) == {N{1'b0}})
    );

endmodule