module register_sva #(parameter WIDTH=8) (
    input logic clk,
    input logic reset,
    input logic xclear,
    input logic xload,
    input logic [WIDTH-1:0] xin,
    input logic [WIDTH-1:0] xout
);
    // Clock: clk (posedge). Reset: reset (active-high, synchronous). Logic: sequential.
    // Behavior: if (xclear||reset) xout<=0; else if (xload) xout<=xin; else hold.

    // Reset drives xout to zero on the next cycle.
    check_reset_clears: assert property (
        @(posedge clk) reset |=> (xout == {WIDTH{1'b0}})
    );

    // Clear drives xout to zero on the next cycle.
    check_xclear_clears: assert property (
        @(posedge clk) xclear |=> (xout == {WIDTH{1'b0}})
    );

    // Clear has priority over load when both are asserted.
    check_clear_overrides_load: assert property (
        @(posedge clk) disable iff (reset) (xclear && xload) |=> (xout == {WIDTH{1'b0}})
    );

    // Load captures xin on the next cycle when no clear.
    check_load_captures_xin: assert property (
        @(posedge clk) disable iff (reset) (xload && !xclear) |=> (xout == $past(xin))
    );

    // When neither load nor clear, xout holds its previous value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!xload && !xclear) |=> (xout == $past(xout))
    );

    // xout only changes following a reset, clear, or load in the previous cycle.
    check_no_spurious_change: assert property (
        @(posedge clk) disable iff (reset) $changed(xout) |-> $past(reset || xclear || xload)
    );

    // With consecutive loads (no clear), the later xin is captured.
    check_two_consecutive_loads_latest_wins: assert property (
        @(posedge clk) disable iff (reset) ($past(xload && !xclear) && (xload && !xclear)) |=> (xout == $past(xin,1))
    );
endmodule