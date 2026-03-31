module my_mac_sva (
    input logic clk,
    input logic reset,
    input logic ce,
    input logic [31:0] din0,
    input logic [31:0] din1,
    input logic [31:0] dout
);

// Reset clears dout on the next cycle.
    check_reset_clears_dout: assert property (
        @(posedge clk) reset |=> (dout == 32'd0)
    );

// With ce low, dout holds its value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (reset) !ce |=> (dout == $past(dout))
    );

// With ce high, dout updates with the previous cycle's din0 * din1.
    check_update_when_ce_high: assert property (
        @(posedge clk) disable iff (reset) ce |=> (dout == $past(dout) + $past(din0) * $past(din1))
    );

// With ce high and din0/din1 zero, dout increments by zero.
    check_zero_product_when_inputs_zero: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 == 32'd0) && (din1 == 32'd0)) |=> (dout == $past(dout))
    );

// With ce high and din0/din1 non-zero, dout increments by the product.
    check_nonzero_product_when_inputs_nonzero: assert property (
        @(posedge clk) disable iff (reset) (ce && (din0 != 32'd0) && (din1 != 32'd0)) |=> (dout == $past(dout) + $past(din0) * $past(din1))
    );

endmodule
