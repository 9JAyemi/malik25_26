module binary_counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic       up_down,
    input logic [3:0] count
);

    // A sampled reset cycle leaves the count at zero on the next sampled clock.
    reset_leaves_count_zero_next_cycle: assert property (
        @(posedge clk) !rst |=> (count == 4'b0000)
    );

    // When reset is released, count is still zero before counting resumes.
    reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == 4'b0000)
    );

    // With up_down high, count increments by one on the next clock.
    count_increments_when_up: assert property (
        @(posedge clk) disable iff (!rst) up_down |=> (count == ($past(count) + 4'b0001))
    );

    // With up_down low, count decrements by one on the next clock.
    count_decrements_when_down: assert property (
        @(posedge clk) disable iff (!rst) !up_down |=> (count == ($past(count) - 4'b0001))
    );

    // Counting up wraps from 4'hF back to 4'h0.
    up_wraps_from_f_to_zero: assert property (
        @(posedge clk) disable iff (!rst) up_down && (count == 4'hF) |=> (count == 4'h0)
    );

    // Counting down wraps from 4'h0 back to 4'hF.
    down_wraps_from_zero_to_f: assert property (
        @(posedge clk) disable iff (!rst) !up_down && (count == 4'h0) |=> (count == 4'hF)
    );

endmodule