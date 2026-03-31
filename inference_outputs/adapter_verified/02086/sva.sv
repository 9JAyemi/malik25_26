module top_module_sva (
    input logic clk,
    input logic reset,       // synchronous active-high
    input logic up_down,
    input logic enable,
    input logic [1:0] q
);

// Reset clears the 8-bit q output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

// With enable=0, q holds its value on the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (q == $past(q))
    );

// With enable=1 and up_down=1, q increments by 1 on the next cycle.
    check_increment_when_enabled_up: assert property (
        @(posedge clk) disable iff (reset)
        (enable && up_down) |=> (q == ($past(q) + 8'h01))
    );

// With enable=1 and up_down=0, q decrements by 1 on the next cycle.
    check_decrement_when_enabled_down: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !up_down) |=> (q == ($past(q) - 8'h01))
    );

// With enable=1 and no change on up_down, q holds its value on the next cycle.
    check_hold_when_enabled_no_toggle: assert property (
        @(posedge clk) disable iff (reset)
        (enable && $stable(up_down)) |=> (q == $past(q))
    );

// With enable=1 and toggle on up_down, q increments by 1 on the next cycle.
    check_increment_when_enabled_toggle: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !$stable(up_down)) |=> (q == ($past(q) + 8'h01))
    );

endmodule
