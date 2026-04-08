module counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled reset cycle forces count to zero by the next clock.
    check_count_zero_after_sampled_reset: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(!reset) |-> (count == 4'd0)
    );

    // On consecutive active samples, count either increments or is zero after an async reset pulse.
    check_count_progresses_or_resets: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $past(reset) |-> ((count == ($past(count) + 4'd1)) || (count == 4'd0))
    );

    // On consecutive active samples, 4'hF wraps back to 4'h0.
    check_wrap_from_max_when_running: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

endmodule