module gray_counter_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic enable,
    input logic [1:0] counter_out,
    input logic [1:0] gray_out
);

    // Reset clears the counter and Gray code on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (counter_out == 2'b00) && (gray_out == 2'b00)
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (counter_out == $past(counter_out))
    );

    // When enabled and counting up, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && up_down) |=> (counter_out == ($past(counter_out) + 2'b01))
    );

    // When enabled and counting down, the counter decrements by one.
    check_decrement_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !up_down) |=> (counter_out == ($past(counter_out) - 2'b01))
    );

    // Gray code 00 maps to counter value 00.
    check_gray_map_00: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b00) |-> (counter_out == 2'b00)
    );

    // Gray code 01 maps to counter value 01.
    check_gray_map_01: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b01) |-> (counter_out == 2'b01)
    );

    // Gray code 11 maps to counter value 11.
    check_gray_map_11: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b11) |-> (counter_out == 2'b11)
    );

    // Gray code 10 maps to counter value 10.
    check_gray_map_10: assert property (
        @(posedge clk) disable iff (reset)
        (gray_out == 2'b10) |-> (counter_out == 2'b10)
    );

    // The functional module output is always the Gray code followed by the counter value.
    check_functional_module_concatenation: assert property (
        @(posedge clk) disable iff (reset)
        (q == {gray_out, counter_out})
    );

endmodule