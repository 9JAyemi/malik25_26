module register_sva (
    input logic clk,
    input logic reset,
    input logic xclear,
    input logic xload,
    input logic [WIDTH-1:0] xin,
    input logic [WIDTH-1:0] xout
);

// Reset forces xout to zero on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (xout == 0)
    );

// xclear forces xout to zero on the next clock.
    check_xclear_clears_output: assert property (
        @(posedge clk) xclear |=> (xout == 0)
    );

// xload captures xin when xclear and reset are low.
    check_xload_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        (xload && !xclear) |=> (xout == $past(xin))
    );

// Without xload, xout holds its previous value.
    check_hold_when_not_loading: assert property (
        @(posedge clk) disable iff (reset)
        (!xload && !xclear) |=> (xout == $past(xout))
    );

// xclear has priority over xload when both are asserted.
    check_xclear_priority_over_xload: assert property (
        @(posedge clk) (xclear && xload) |=> (xout == 0)
    );

endmodule
