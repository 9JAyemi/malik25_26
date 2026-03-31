module my_mac_sva (
    input logic clk,
    input logic reset,     // active-high synchronous reset
    input logic ce,
    input logic [31:0] din0,
    input logic [31:0] din1,
    input logic [31:0] dout
);
    // Reset sets dout to 0 on the next cycle.
    reset_clears_dout_next: assert property (
        @(posedge clk) reset |-> (dout == 32'd0)
    );

    // While reset stays asserted (2+ cycles), dout is 0.
    reset_holds_zero_while_asserted: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (dout == 32'd0)
    );

    // When ce is LOW and prior cycle was not reset, dout holds its value.
    hold_when_ce_low: assert property (
        @(posedge clk) disable iff (reset) (!ce && !$past(reset)) |-> (dout == $past(dout))
    );

    // When ce is HIGH, dout accumulates din0*din1 modulo 2^32 on the next cycle.
    accumulates_on_ce: assert property (
        @(posedge clk) disable iff (reset) ce |-> (dout == (($past(dout) + ($past(din0) * $past(din1)))[31:0]))
    );

    // Any change in dout (not due to reset) implies ce was HIGH in the previous cycle.
    change_requires_ce_prev: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (dout != $past(dout))) |-> $past(ce)
    );

    // If ce is HIGH and either operand is zero, dout does not change next cycle.
    zero_operand_no_change: assert property (
        @(posedge clk) disable iff (reset) (ce && ((din0 == 32'd0) || (din1 == 32'd0))) |-> (dout == $past(dout))
    );

    // If ce is HIGH and previous dout was zero, next dout equals product LSBs.
    accumulate_from_zero: assert property (
        @(posedge clk) disable iff (reset) (ce && ($past(dout) == 32'd0)) |-> (dout == (($past(din0) * $past(din1))[31:0]))
    );

    // Two consecutive ce cycles accumulate two products modulo 2^32.
    two_cycle_accumulate: assert property (
        @(posedge clk) disable iff (reset)
            (ce && $past(ce,1) && !$past(reset,1) && !$past(reset,2)) |->
            (dout == (($past(dout,2) +
                       ($past(din0,2) * $past(din1,2)) +
                       ($past(din0,1) * $past(din1,1)))[31:0]))
    );

    // If ce is HIGH and din0 is 1, next dout increments by din1 modulo 2^32.
    unit_din0_increments_by_din1: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'd1)) |-> (dout == (($past(dout) + $past(din1))[31:0]))
    );

    // If ce is HIGH and din1 is 1, next dout increments by din0 modulo 2^32.
    unit_din1_increments_by_din0: assert property (
        @(posedge clk) disable iff (reset) (ce && (din1 == 32'd1)) |-> (dout == (($past(dout) + $past(din0))[31:0]))
    );
endmodule