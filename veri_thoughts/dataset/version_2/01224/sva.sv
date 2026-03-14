module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] Q
);
    // While reset is HIGH, Q must be 0 at each sampled clock edge.
    reset_forces_zero: assert property (
        @(posedge clk) reset |-> (Q == 4'b0000)
    );

    // When not in reset and enable is HIGH, Q increments by 1 (mod 16).
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |-> (Q == $past(Q) + 4'd1)
    );

    // When not in reset and enable is LOW, Q holds its value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |-> (Q == $past(Q))
    );

    // Any change in Q (without reset) implies enable is HIGH that cycle.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (Q != $past(Q)) |-> enable
    );

    // Wrap-around: if previous Q was 15 and enable is HIGH, Q becomes 0.
    wrap_from_15_to_0_on_enable: assert property (
        @(posedge clk) disable iff (reset) (enable && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );

    // After 16 consecutive enabled cycles (no reset), Q returns to its original value.
    full_cycle_after_16_enables: assert property (
        @(posedge clk) disable iff (reset) enable[*16] |-> (Q == $past(Q,16))
    );

    // On reset deassertion with enable LOW, Q remains 0 on that cycle.
    reset_release_no_enable_keeps_zero: assert property (
        @(posedge clk) ($fell(reset) && !enable) |-> (Q == 4'h0)
    );

    // On reset deassertion with enable HIGH, Q becomes 1 on that cycle.
    reset_release_with_enable_sets_one: assert property (
        @(posedge clk) ($fell(reset) && enable) |-> (Q == 4'h1)
    );
endmodule