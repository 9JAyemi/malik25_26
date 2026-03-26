module dff_ras_sva (
    input logic clk,
    input logic reset,
    input logic set,
    input logic d,
    input logic q
);

    // Reset drives q low.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 1'b0)
    );

    // Reset has priority over set.
    check_reset_priority_over_set: assert property (
        @(posedge clk) (reset && set) |=> (q == 1'b0)
    );

    // Set drives q high when reset is low.
    check_set_drives_q_high: assert property (
        @(posedge clk) disable iff (reset) set |=> (q == 1'b1)
    );

    // Set overrides d when d is low.
    check_set_priority_over_d_low: assert property (
        @(posedge clk) disable iff (reset) (set && (d == 1'b0)) |=> (q == 1'b1)
    );

    // q captures d=1 when reset and set are low.
    check_data_capture_one: assert property (
        @(posedge clk) disable iff (reset) (!set && (d == 1'b1)) |=> (q == 1'b1)
    );

    // q captures d=0 when reset and set are low.
    check_data_capture_zero: assert property (
        @(posedge clk) disable iff (reset) (!set && (d == 1'b0)) |=> (q == 1'b0)
    );

endmodule