module binary_counter_sva (
    input  logic       clk,
    input  logic       reset,   // active-high synchronous reset
    input  logic       enable,
    input  logic [3:0] count
);
    // Synchronous reset drives count to 0 on the next cycle.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // While reset is held, count stays 0 (checked each cycle via prior-cycle reset).
    count_zero_while_reset: assert property (
        @(posedge clk) $past(reset) |-> (count == 4'd0)
    );

    // Reset dominates enable when both are asserted.
    reset_overrides_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'd0)
    );

    // When enabled (and not in reset), count increments by 1.
    increment_on_enable: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When not enabled (and not in reset), count holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // A change in count implies enable was high in the previous cycle (excluding reset).
    change_only_on_enable: assert property (
        @(posedge clk) disable iff (reset) $changed(count) |-> $past(enable)
    );

    // With enable and previous count = 4'hF, wrap to 4'h0 next cycle.
    wrap_from_15_to_0: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) == 4'hF)) |=> (count == 4'h0)
    );

    // Exact sequential update rule across cycles (including reset and enable).
    exact_update_rule: assert property (
        @(posedge clk)
            $past(1'b1) |-> ( $past(reset)
                              ? (count == 4'd0)
                              : (count == ($past(enable) ? ($past(count) + 4'd1) : $past(count))) )
    );
endmodule