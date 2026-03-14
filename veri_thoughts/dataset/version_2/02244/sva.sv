module binary_counter_sva (
    input logic clk,
    input logic rst,      // active-high synchronous reset
    input logic en,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (active-high, synchronous). Sequential 4-bit counter: reset->0; if en: +1 with wrap at 15; else hold.

    // On any cycle with rst asserted, next count must be 0.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

    // When en is LOW (and not in reset), count holds its previous value.
    count_holds_when_en_low: assert property (
        @(posedge clk) disable iff (rst) (!en) |=> (count == $past(count, 1, rst))
    );

    // When en is HIGH and count is not 15, next count increments by 1.
    count_increments_when_en_not_max: assert property (
        @(posedge clk) disable iff (rst) (en && (count != 4'hF)) |=> (count == $past(count, 1, rst) + 4'd1)
    );

    // When en is HIGH and count is 15, next count wraps to 0.
    count_wraps_on_max_when_en: assert property (
        @(posedge clk) disable iff (rst) (en && (count == 4'hF)) |=> (count == 4'h0)
    );

    // With en HIGH (and not in reset), count must change next cycle.
    enabled_always_changes_count: assert property (
        @(posedge clk) disable iff (rst) en |=> (count != $past(count, 1, rst))
    );

    // Any change in count must be caused by prior en or prior rst.
    count_change_requires_en_or_rst: assert property (
        @(posedge clk) disable iff (rst) (count != $past(count, 1, rst)) |-> ($past(rst) || $past(en, 1, rst))
    );

    // With en HIGH and not at max, next count must not be 0 (no spurious clear).
    no_unexpected_zero_on_en_not_max: assert property (
        @(posedge clk) disable iff (rst) (en && (count != 4'hF)) |=> (count != 4'h0)
    );

    // If prior cycle had en HIGH and not in reset, a 0 value now implies prior count was 15.
    zero_now_implies_prev_max_when_prev_en: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst && en, 1, rst) && (count == 4'h0)) |-> ($past(count, 1, rst) == 4'hF)
    );

endmodule