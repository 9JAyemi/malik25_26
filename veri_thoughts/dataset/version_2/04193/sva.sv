module sync_load_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic [3:0] L,
    input logic areset,
    input logic [3:0] count,
    input logic [3:0] count_reg1,
    input logic [3:0] count_reg2
);

    // Sync reset forces count to zero on the next clock.
    check_sync_reset_clears_count: assert property (
        @(posedge clk) disable iff (!areset)
        reset |=> (count == 4'd0)
    );

    // Load copies L into count on the next clock when reset is low.
    check_load_captures_L: assert property (
        @(posedge clk) disable iff (!areset)
        (!reset && load) |=> (count == $past(L))
    );

    // Free-running mode increments from count_reg1 on the next clock.
    check_free_run_increments_from_count_reg1: assert property (
        @(posedge clk) disable iff (!areset)
        (!reset && !load) |=> (count == ($past(count_reg1) + 4'd1))
    );

    // Reset has priority over load in the count update logic.
    check_reset_overrides_load: assert property (
        @(posedge clk) disable iff (!areset)
        (reset && load) |=> (count == 4'd0)
    );

    // A sampled async reset leaves both pipeline registers cleared.
    check_async_reset_clears_pipe_regs: assert property (
        @(posedge clk) disable iff (!areset)
        (!$past(areset)) |-> ((count_reg1 == 4'd0) && (count_reg2 == 4'd0))
    );

    // The first free-running cycle after a sampled async reset produces 1.
    check_async_reset_recovery_counts_one: assert property (
        @(posedge clk) disable iff (!areset)
        ((!$past(areset)) && !reset && !load) |=> (count == 4'd1)
    );

endmodule