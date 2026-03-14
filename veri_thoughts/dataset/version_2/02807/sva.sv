module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // On reset, count is driven to zero on that clock edge.
    reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // Functional update when not in reset: increment on enable, else hold.
    functional_update_rule: assert property (
        @(posedge clk) disable iff (reset) count == ($past(count) + (enable ? 4'd1 : 4'd0))
    );

    // When not in reset and enable is high, count increments by 1 (mod 16).
    increment_when_enable: assert property (
        @(posedge clk) disable iff (reset) enable |-> (count == ($past(count) + 4'd1))
    );

    // When not in reset and enable is low, count holds its previous value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> (count == $past(count))
    );

    // Any change to count (outside reset) implies enable is high.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> enable
    );

    // If previous count was 15 and enable is high (no reset), wrap to 0.
    wrap_on_enable_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );
endmodule