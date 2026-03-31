module my_mac_sva (
    input logic clk,
    input logic reset,
    input logic ce,
    input logic [31:0] din0,
    input logic [31:0] din1,
    input logic [31:0] dout
);
    // Reset drives dout to zero on the next cycle.
    reset_clears_dout_next: assert property (
        @(posedge clk) reset |=> (dout == 32'd0)
    );

    // With ce high, dout accumulates din0*din1 (mod 2^32) on the next cycle.
    accumulate_on_ce: assert property (
        @(posedge clk) disable iff (reset) ce |=> (dout == $past(dout) + $past(din0) * $past(din1))
    );

    // With ce low, dout holds its value on the next cycle.
    hold_when_ce_low: assert property (
        @(posedge clk) disable iff (reset) !ce |=> (dout == $past(dout))
    );

    // Any change in dout must be caused by reset or ce high in the prior cycle.
    change_requires_reset_or_ce: assert property (
        @(posedge clk) disable iff (reset) (dout != $past(dout)) |-> ($past(reset) || $past(ce))
    );

    // If reset and ce are both high, reset has priority and dout becomes zero next cycle.
    reset_overrides_ce: assert property (
        @(posedge clk) (reset && ce) |=> (dout == 32'd0)
    );

    // With ce high and either operand zero, dout holds its value next cycle.
    zero_operand_keeps_dout: assert property (
        @(posedge clk) disable iff (reset) (ce && ((din0 == 32'd0) || (din1 == 32'd0))) |=> (dout == $past(dout))
    );

    // With ce high and both operands one, dout increments by one next cycle.
    increment_on_one_operands: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'd1) && (din1 == 32'd1)) |=> (dout == $past(dout) + 32'd1)
    );

    // With ce high and both operands 32'hFFFF, dout increments by 32'hFFFF next cycle.
    increment_on_max_operands: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'hFFFF) && (din1 == 32'hFFFF)) |=> (dout == $past(dout) + 32'hFFFF)
    );

    // With ce high and both operands 32'h80000000, dout decrements by 32'h80000000 next cycle.
    decrement_on_min_operands: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'h80000000) && (din1 == 32'h80000000)) |=> (dout == $past(dout) - 32'h80000000)
    );

    // With ce high and both operands 32'hFFFFFFFF, dout becomes zero next cycle.
    zero_on_all_ones: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'hFFFFFFFF) && (din1 == 32'hFFFFFFFF)) |=> (dout == 32'd0)
    );
endmodule