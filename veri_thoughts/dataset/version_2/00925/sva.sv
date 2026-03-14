module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] q
);
    ///// Reset behavior /////
    // When reset is asserted at the clock edge, q is driven to 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (q == 4'b0000)
    );

    // If reset is asserted in consecutive cycles, q stays 0 across both cycles.
    check_hold_zero_during_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'b0000 && $past(q) == 4'b0000)
    );

    // If the previous cycle was in reset, q in that previous cycle was 0.
    check_prev_cycle_zero_during_reset: assert property (
        @(posedge clk) $past(reset) |-> ($past(q) == 4'b0000)
    );

    ///// Exit from reset /////
    // On the first cycle out of reset, q becomes 1.
    check_out_of_reset_starts_at_one: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset) |-> (q == 4'b0001)
    );

    // If reset is high now, next cycle q is 0 if reset stays high, else 1.
    check_next_cycle_after_reset: assert property (
        @(posedge clk) reset |=> (reset ? (q == 4'b0000) : (q == 4'b0001))
    );

    ///// Sanity /////
    // q is never X/Z when not in reset.
    check_q_known_out_of_reset: assert property (
        @(posedge clk) disable iff (reset) !$isunknown(q)
    );

    // With reset low, q==0 can only occur due to wrap-around from 0xF (or if previous cycle was in reset).
    check_zero_only_from_wrap: assert property (
        @(posedge clk) disable iff (reset) (q == 4'b0000) |-> ($past(q) == 4'b1111 || $past(reset))
    );

    // With reset low in consecutive cycles, q cannot remain 0 (no 0->0 stutter).
    check_no_stutter_zero_out_of_reset: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) == 1'b0 && reset == 1'b0 && $past(q) == 4'b0000) |-> (q != 4'b0000)
    );
endmodule