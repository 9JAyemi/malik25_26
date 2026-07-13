module clk_gen_sva (
    input logic clk100MHz,
    input logic rst,
    input logic clk_4sec,
    input logic clk_5KHz,
    input integer count,
    input integer count1
);

    // Reset clears both counters and both generated clocks.
    check_reset_clears_state: assert property (
        @(posedge clk100MHz)
        (!rst) |-> ((count == 0) && (count1 == 0) && (clk_4sec == 1'b0) && (clk_5KHz == 1'b0))
    );

    // The first active clock after reset release increments both counters to 1.
    check_first_cycle_after_reset_release: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        $rose(rst) |-> ((count == 1) && (count1 == 1) && (clk_4sec == 1'b0) && (clk_5KHz == 1'b0))
    );

    // count increments by one whenever it is not at its terminal value.
    check_count_increments_below_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count != 200000000) |=> (count == ($past(count) + 1))
    );

    // clk_4sec stays unchanged whenever count is not at its terminal value.
    check_clk_4sec_stable_below_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count != 200000000) |=> $stable(clk_4sec)
    );

    // count wraps to 1 after reaching its terminal value.
    check_count_wraps_at_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count == 200000000) |=> (count == 1)
    );

    // clk_4sec toggles when count reaches its terminal value.
    check_clk_4sec_toggles_at_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count == 200000000) |=> (clk_4sec != $past(clk_4sec))
    );

    // count1 increments by one whenever it is not at its terminal value.
    check_count1_increments_below_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count1 != 10000) |=> (count1 == ($past(count1) + 1))
    );

    // clk_5KHz stays unchanged whenever count1 is not at its terminal value.
    check_clk_5khz_stable_below_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count1 != 10000) |=> $stable(clk_5KHz)
    );

    // count1 wraps to 1 after reaching its terminal value.
    check_count1_wraps_at_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count1 == 10000) |=> (count1 == 1)
    );

    // clk_5KHz toggles when count1 reaches its terminal value.
    check_clk_5khz_toggles_at_terminal: assert property (
        @(posedge clk100MHz) disable iff (!rst)
        (count1 == 10000) |=> (clk_5KHz != $past(clk_5KHz))
    );

endmodule