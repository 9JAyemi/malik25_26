module sync_reset_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Sampled active-low reset forces count to zero.
    check_reset_drives_zero: assert property (
        @(posedge clk) !rst |-> (count == 4'd0)
    );

    // First clock after a sampled reset low sets count to one.
    check_reset_release_starts_at_one: assert property (
        @(posedge clk) disable iff (!rst) (!$past(rst)) |-> (count == 4'd1)
    );

    // With reset high on consecutive samples, count increments or restarts from one after an async reset pulse.
    check_running_step_or_restart: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> ((count == ($past(count) + 4'd1)) || (count == 4'd1))
    );

    // A sampled zero while running can only come from wrapping past 15.
    check_zero_only_after_wrap: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && (count == 4'd0)) |-> ($past(count) == 4'hF)
    );

    // A sampled zero while running advances to one on the next clock.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && ($past(count) == 4'd0)) |-> (count == 4'd1)
    );

endmodule