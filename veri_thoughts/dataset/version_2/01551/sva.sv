module d_ff_sva (
    input logic clk,
    input logic reset_n,
    input logic enable,
    input logic d,
    input logic q
);
    // Clock: clk (posedge). Reset: reset_n (active-low, asynchronous). Sequential DFF with enable.

    // Reset low forces q to 0 on every clock edge while asserted.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset_n |-> (q == 1'b0)
    );

    // With reset high in consecutive cycles, q follows next-state: q = (enable ? d : hold).
    check_next_state_when_reset_high: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (q == ($past(enable) ? $past(d) : $past(q)))
    );

    // First cycle after reset (prev reset low): if enable is 0, q must remain 0.
    check_post_reset_hold_zero_if_disabled: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(!reset_n) && !enable) |-> (q == 1'b0)
    );

    // First cycle after reset (prev reset low): if enable is 1, q updates to current d.
    check_post_reset_update_if_enabled: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(!reset_n) && enable) |-> (q == d)
    );
endmodule