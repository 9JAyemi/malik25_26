module sync_debouncer_10ms_sva (
    input logic        signal_debounced,
    input logic        clk_50mhz,
    input logic        rst,
    input logic        signal_async,
    input logic [1:0]  sync_stage,
    input logic [18:0] debounce_counter
);

    wire signal_sync = sync_stage[1];
    wire debounce_counter_done = (debounce_counter == 19'h7ffff);

    // Reset drives all sequential state to zero.
    check_reset_state: assert property (
        @(posedge clk_50mhz)
        rst |-> (sync_stage == 2'b00) &&
                (debounce_counter == 19'h00000) &&
                (signal_debounced == 1'b0)
    );

    // The first synchronizer stage samples the async input.
    check_sync_stage_lsb_capture: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) |-> (sync_stage[0] == $past(signal_async))
    );

    // The second synchronizer stage samples the first stage.
    check_sync_stage_msb_capture: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) |-> (sync_stage[1] == $past(sync_stage[0]))
    );

    // The debounce counter clears when the debounced output matches the synchronized input.
    check_counter_clears_on_match: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) && $past(signal_debounced == signal_sync) |-> (debounce_counter == 19'h00000)
    );

    // The debounce counter increments while mismatch persists below terminal count.
    check_counter_increments_on_mismatch: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) &&
        $past((signal_debounced != signal_sync) && (debounce_counter != 19'h7ffff))
        |-> (debounce_counter == ($past(debounce_counter) + 19'h00001))
    );

    // The debounce counter wraps to zero after terminal count on a mismatch.
    check_counter_wraps_after_terminal_count: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) &&
        $past((signal_debounced != signal_sync) && (debounce_counter == 19'h7ffff))
        |-> (debounce_counter == 19'h00000)
    );

    // The debounced output toggles when terminal count was reached.
    check_output_toggles_on_terminal_count: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) && $past(debounce_counter_done) |-> (signal_debounced == ~$past(signal_debounced))
    );

    // The debounced output holds its value when terminal count was not reached.
    check_output_holds_without_terminal_count: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) && !$past(debounce_counter_done) |-> (signal_debounced == $past(signal_debounced))
    );

    // Any output change must be caused by terminal count.
    check_output_change_requires_terminal_count: assert property (
        @(posedge clk_50mhz) disable iff (rst)
        !$past(rst) && (signal_debounced != $past(signal_debounced)) |-> $past(debounce_counter_done)
    );

endmodule