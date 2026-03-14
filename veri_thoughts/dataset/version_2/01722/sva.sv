module ExtToIntSync_sva (
    input logic clk,
    input logic rst,
    input logic ext_signal,
    input logic int_signal
);
    // When reset is HIGH at the clock edge, int_signal is driven to 0 in the same cycle.
    check_reset_sets_zero_now: assert property (
        @(posedge clk) rst |-> ##0 (int_signal == 1'b0)
    );

    // If reset is HIGH in two consecutive samples, int_signal must read as 0 now.
    check_reset_held_zero: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (int_signal == 1'b0)
    );

    // Immediately after reset deasserts, sampled int_signal remains 0 from the prior cycle.
    check_post_reset_sample_zero: assert property (
        @(posedge clk) $fell(rst) |-> (int_signal == 1'b0)
    );

    // With reset LOW, int_signal captures ext_signal on the same clock edge (after NBA).
    check_capture_when_not_reset: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> ##0 (int_signal == ext_signal)
    );

    // If reset is HIGH now, int_signal is 0 on the next sampled cycle.
    check_reset_implies_next_zero: assert property (
        @(posedge clk) rst |=> (int_signal == 1'b0)
    );

    // On a sampled rising edge of reset, int_signal is driven to 0 in the same cycle.
    check_reset_rise_sets_zero_now: assert property (
        @(posedge clk) $rose(rst) |-> ##0 (int_signal == 1'b0)
    );
endmodule