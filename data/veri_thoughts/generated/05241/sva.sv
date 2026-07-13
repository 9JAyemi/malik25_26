module synchronizer_assertions (
    input logic async_in,
    input logic clk_in,
    input logic sync_out,
    input logic async_sync,
    input logic async_sync_prev
);

    // First stage samples async_in on each rising clock edge.
    check_async_sync_captures_input: assert property (
        @(posedge clk_in) disable iff ($initstate)
        async_sync == $past(async_in)
    );

    // Previous-stage register holds the prior async_sync value.
    check_async_sync_prev_captures_first_stage: assert property (
        @(posedge clk_in) disable iff ($initstate)
        async_sync_prev == $past(async_sync)
    );

    // sync_out holds the prior async_sync value.
    check_sync_out_captures_first_stage: assert property (
        @(posedge clk_in) disable iff ($initstate)
        sync_out == $past(async_sync)
    );

    // sync_out and async_sync_prev are loaded from the same source.
    check_sync_out_matches_prev_stage: assert property (
        @(posedge clk_in) disable iff ($initstate)
        sync_out == async_sync_prev
    );

    // After pipeline fill, sync_out is async_in delayed by two sampled clocks.
    check_sync_out_two_cycle_delay_from_input: assert property (
        @(posedge clk_in) disable iff ($initstate)
        !$past($initstate) |-> sync_out == $past(async_in, 2)
    );

endmodule