module dff_rs_sva (
    input logic clk,
    input logic rst,
    input logic set,
    input logic d,
    input logic q
);

    // Reset forces q low on the following cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (q == 1'b0)
    );

    // Reset has priority over set when both are asserted.
    check_reset_priority_over_set: assert property (
        @(posedge clk) (rst && set) |=> (q == 1'b0)
    );

    // Set drives q high when reset is not asserted.
    check_set_drives_q_high: assert property (
        @(posedge clk) disable iff (rst) set |=> (q == 1'b1)
    );

    // Set overrides d when d is low.
    check_set_priority_over_d: assert property (
        @(posedge clk) disable iff (rst) (set && !d) |=> (q == 1'b1)
    );

    // With no reset or set, d=1 is captured into q.
    check_capture_d_high: assert property (
        @(posedge clk) disable iff (rst) (!set && d) |=> (q == 1'b1)
    );

    // With no reset or set, d=0 is captured into q.
    check_capture_d_low: assert property (
        @(posedge clk) disable iff (rst) (!set && !d) |=> (q == 1'b0)
    );

endmodule