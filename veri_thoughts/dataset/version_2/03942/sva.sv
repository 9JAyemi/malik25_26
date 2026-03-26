module dff_asr_sva (
    input logic clk,
    input logic d,
    input logic set,
    input logic reset,
    input logic q,
    input logic q_n
);

    // No assertion-disabling reset exists; set and reset are synchronous controls.

    // Set forces q high and q_n low on the next clock.
    check_set_behavior: assert property (
        @(posedge clk) disable iff (1'b0)
            set |=> (q == 1'b1 && q_n == 1'b0)
    );

    // Reset forces q low and q_n high when set is low.
    check_reset_behavior: assert property (
        @(posedge clk) disable iff (1'b0)
            (!set && reset) |=> (q == 1'b0 && q_n == 1'b1)
    );

    // With set and reset low, d=1 is captured on the next clock.
    check_capture_one: assert property (
        @(posedge clk) disable iff (1'b0)
            (!set && !reset && d) |=> (q == 1'b1 && q_n == 1'b0)
    );

    // With set and reset low, d=0 is captured on the next clock.
    check_capture_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            (!set && !reset && !d) |=> (q == 1'b0 && q_n == 1'b1)
    );

    // If set and reset are both high, set has priority.
    check_set_priority: assert property (
        @(posedge clk) disable iff (1'b0)
            (set && reset) |=> (q == 1'b1 && q_n == 1'b0)
    );

    // After each clocked update, q and q_n remain complementary.
    check_complementary_outputs: assert property (
        @(posedge clk) disable iff (1'b0)
            1'b1 |=> (q_n == ~q)
    );

endmodule