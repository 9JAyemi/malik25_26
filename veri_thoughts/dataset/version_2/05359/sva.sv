module ff_sync_set_clear_assertions (
    input logic clk,
    input logic d,
    input logic set,
    input logic clr,
    input logic q
);

    // set drives q high on the next clock.
    check_set_forces_q_high: assert property (
        @(posedge clk) set |=> (q == 1'b1)
    );

    // set has priority over clr when both are high.
    check_set_overrides_clear: assert property (
        @(posedge clk) (set && clr) |=> (q == 1'b1)
    );

    // clr drives q low when set is not asserted.
    check_clear_forces_q_low: assert property (
        @(posedge clk) (!set && clr) |=> (q == 1'b0)
    );

    // d=1 is captured when neither set nor clr is asserted.
    check_data_one_captured: assert property (
        @(posedge clk) (!set && !clr && d) |=> (q == 1'b1)
    );

    // d=0 is captured when neither set nor clr is asserted.
    check_data_zero_captured: assert property (
        @(posedge clk) (!set && !clr && !d) |=> (q == 1'b0)
    );

endmodule