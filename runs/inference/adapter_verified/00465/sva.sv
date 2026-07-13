module up_counter_2bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [1:0] count
);

// Reset drives count to 0 on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 2'b00)
    );

// When enable is low, count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

// When enable is high, count increments by 1 (mod 4).
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 2'b01))
    );

// Incrementing from 3 wraps count back to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 2'b11)) |=> (count == 2'b00)
    );

endmodule
