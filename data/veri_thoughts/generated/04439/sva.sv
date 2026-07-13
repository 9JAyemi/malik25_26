module dff_rst_set_clr_sva (
    input logic clk,
    input logic rst,
    input logic set,
    input logic clr,
    input logic d,
    input logic q
);

    // A low reset drives q low by the next clock sample.
    check_reset_clears_q: assert property (
        @(posedge clk)
        !rst |=> (q == 1'b0)
    );

    // Set drives q high on the next cycle.
    check_set_loads_high: assert property (
        @(posedge clk) disable iff (!rst)
        set |=> (q == 1'b1)
    );

    // Clear drives q low when set is not asserted.
    check_clear_loads_low: assert property (
        @(posedge clk) disable iff (!rst)
        (!set && clr) |=> (q == 1'b0)
    );

    // Data value 1 is loaded when set and clear are both low.
    check_data_one_loads_high: assert property (
        @(posedge clk) disable iff (!rst)
        (!set && !clr && d) |=> (q == 1'b1)
    );

    // Data value 0 is loaded when set and clear are both low.
    check_data_zero_loads_low: assert property (
        @(posedge clk) disable iff (!rst)
        (!set && !clr && !d) |=> (q == 1'b0)
    );

    // Set has priority over clear when both are asserted.
    check_set_priority_over_clear: assert property (
        @(posedge clk) disable iff (!rst)
        (set && clr) |=> (q == 1'b1)
    );

endmodule