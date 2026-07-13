module counter_sva #(
    parameter HIGH = 1'b1,
    parameter LOW  = 1'b0
)(
    input logic       CLK,
    input logic       RESET,
    input logic       ENABLE,
    input logic [3:0] COUNT
);

    // Reset clears COUNT on the following clock.
    check_reset_clears_count: assert property (
        @(posedge CLK)
        (RESET == HIGH) |=> (COUNT == 4'h0)
    );

    // Reset overrides ENABLE when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge CLK)
        ((RESET == HIGH) && (ENABLE == HIGH)) |=> (COUNT == 4'h0)
    );

    // ENABLE causes COUNT to increment by one outside reset.
    check_increment_when_enabled: assert property (
        @(posedge CLK) disable iff (RESET == HIGH)
        (ENABLE == HIGH) |=> (COUNT == ($past(COUNT) + 4'd1))
    );

    // COUNT holds when ENABLE is low outside reset.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RESET == HIGH)
        (ENABLE == LOW) |=> (COUNT == $past(COUNT))
    );

    // The 4-bit counter wraps from 15 to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge CLK) disable iff (RESET == HIGH)
        ((ENABLE == HIGH) && (COUNT == 4'hF)) |=> (COUNT == 4'h0)
    );

endmodule