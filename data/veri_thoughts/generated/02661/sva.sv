module dff_async_rst_sva (
    input logic clk,
    input logic rst,
    input logic d,
    input logic en,
    input logic q
);
    // Clock: clk (posedge), Reset: rst active-low asynchronous, Sequential DFF with enable.

    // While reset is held LOW across consecutive cycles, q must be 0.
    check_q_zero_while_reset_low: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (q == 1'b0)
    );

    // While reset remains LOW across consecutive cycles, q is stable.
    check_q_stable_while_reset_low: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (q == $past(q))
    );

    // On reset deassertion (0->1), q is 0 at that clock edge.
    check_q_zero_on_reset_deassert: assert property (
        @(posedge clk) $rose(rst) |-> (q == 1'b0)
    );

    // With enable LOW in the previous cycle and not in reset now, q holds or is 0 if an async reset occurred mid-cycle.
    check_hold_when_en_low_or_reset_midcycle: assert property (
        @(posedge clk) disable iff (!rst) !$past(en) |-> (q == $past(q) || q == 1'b0)
    );

    // With enable HIGH in the previous cycle and not in reset now, q captures previous d or is 0 if an async reset occurred mid-cycle.
    check_capture_when_en_high_or_reset_midcycle: assert property (
        @(posedge clk) disable iff (!rst) $past(en) |-> (q == $past(d) || q == 1'b0)
    );

    // Immediately after reset deassertion with enable HIGH, next cycle q equals this cycle's d if still out of reset.
    check_capture_after_reset_deassert_with_en: assert property (
        @(posedge clk) ($rose(rst) && en) |=> ( rst ? (q == $past(d)) : 1'b1 )
    );
endmodule