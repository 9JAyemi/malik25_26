module register_sva #(parameter WIDTH=8) (
    input logic clk,
    input logic reset,
    input logic xclear,
    input logic xload,
    input logic [WIDTH-1:0] xin,
    input logic [WIDTH-1:0] xout
);

    // Reset or xclear forces xout to zero on the next cycle.
    check_reset_or_xclear_clears_output: assert property (
        @(posedge clk) disable iff (reset)
        (xclear || reset) |=> (xout == '0)
    );

    // With neither reset nor xclear, xout holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        !(xclear || reset) |=> (xout == $past(xout))
    );

    // With neither reset nor xclear and xload high, xout loads xin.
    check_load_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        !(xclear || reset) && xload |=> (xout == $past(xin))
    );

    // With neither reset nor xclear and xload low, xout holds its value.
    check_hold_when_load_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !(xclear || reset) && !xload |=> (xout == $past(xout))
    );

endmodule