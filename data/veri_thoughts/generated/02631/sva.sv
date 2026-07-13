module up_counter_sva (
    input logic clk,
    input logic rst,      // active-high, synchronous reset
    input logic en,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (active-high, synchronous). Logic: sequential counter with enable.

    // Reset sets count to 0 on the next clock.
    check_reset_sets_zero_next: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // While reset is held for 2+ cycles, count reads as 0 each cycle.
    check_reset_keeps_zero_while_held: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0)
    );

    // When en is low and not in reset, count holds its value.
    check_hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst) (!en) |=> (count == $past(count))
    );

    // When en is high and not in reset, count increments modulo 16.
    check_increment_mod16_when_en_high: assert property (
        @(posedge clk) disable iff (rst) en |=> (count == (($past(count) + 4'd1) & 4'hF))
    );

    // Any count change must be caused by prior en or reset.
    check_change_requires_prev_en_or_rst: assert property (
        @(posedge clk) disable iff (rst) (count != $past(count)) |-> ($past(en) || $past(rst))
    );

    // If prior en was high and not in reset, count changes next cycle.
    check_progress_on_prev_enable: assert property (
        @(posedge clk) disable iff (rst) ($past(en) && !$past(rst)) |-> (count != $past(count))
    );

    // If both rst and en were high last cycle, reset takes priority (count becomes 0).
    check_reset_overrides_enable: assert property (
        @(posedge clk) ($past(rst) && $past(en)) |-> (count == 4'd0)
    );

    // If prior en was high and prior count was 4'hF, next count wraps to 0.
    check_wrap_from_max_on_enable: assert property (
        @(posedge clk) disable iff (rst) ($past(en) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );
endmodule