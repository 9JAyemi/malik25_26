module zl_reset_sync_sva (
    input logic clk,
    input logic in_rst_n,
    input logic out_rst_n
);
    // Clock: clk (posedge). Reset: in_rst_n active-LOW, asynchronous. Sequential two-flop reset synchronizer.

    // When input reset is asserted LOW, output reset must be LOW.
    check_reset_forces_out_low: assert property (
        @(posedge clk) !in_rst_n |-> (out_rst_n == 1'b0)
    );

    // Output reset HIGH only when input reset is HIGH.
    check_out_high_requires_in_high: assert property (
        @(posedge clk) disable iff (!in_rst_n) out_rst_n |-> in_rst_n
    );

    // On sampled falling edge of in_rst_n, out_rst_n is LOW in the same cycle.
    check_reset_fall_forces_out_low_now: assert property (
        @(posedge clk) $fell(in_rst_n) |-> (out_rst_n == 1'b0)
    );

    // After a sampled falling edge of in_rst_n, out_rst_n remains LOW in the next cycle.
    check_reset_fall_keeps_out_low_next: assert property (
        @(posedge clk) $fell(in_rst_n) |-> ##1 (out_rst_n == 1'b0)
    );

    // On sampled rising edge of in_rst_n, out_rst_n is still LOW in that cycle.
    check_out_low_on_reset_rise: assert property (
        @(posedge clk) $rose(in_rst_n) |-> (out_rst_n == 1'b0)
    );

    // Rising edge of out_rst_n requires in_rst_n HIGH in both current and previous cycle.
    check_out_rise_requires_in_high_now_and_prev: assert property (
        @(posedge clk) disable iff (!in_rst_n) $rose(out_rst_n) |-> (in_rst_n && $past(in_rst_n))
    );

    // No back-to-back rising edges on out_rst_n.
    check_no_back_to_back_out_rises: assert property (
        @(posedge clk) disable iff (!in_rst_n) $rose(out_rst_n) |-> ##1 (!$rose(out_rst_n))
    );

    // If in_rst_n is LOW for two consecutive cycles, out_rst_n is LOW at the second cycle.
    check_persistent_reset_low_ensures_out_low: assert property (
        @(posedge clk) (!in_rst_n)[*2] |-> (out_rst_n == 1'b0)
    );
endmodule