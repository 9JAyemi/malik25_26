module assert_time_assert_sva #(
    parameter [31:0] num_cks = 32'd1000
) (
    input logic clk,
    input logic reset_n,
    input logic start_event,
    input logic test_expr,
    input logic [31:0] window,
    input logic ignore_new_start,
    input logic reset_on_new_start,
    input logic error_on_new_start,
    input logic xzcheck_enable,
    input logic assertion,
    input logic [31:0] timer,
    input logic active,
    input logic [31:0] num_cks_counter
);

    // Counter increments when it has not reached the terminal count.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter != num_cks)
        |=> (num_cks_counter == ($past(num_cks_counter) + 32'd1))
    );

    // Counter resets to zero on the terminal count.
    check_counter_wraps_to_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks)
        |=> (num_cks_counter == 32'd0)
    );

    // State holds on cycles where the terminal count is not hit.
    check_state_holds_between_terminal_counts: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter != num_cks)
        |=> (timer == $past(timer)) &&
            (active == $past(active)) &&
            (assertion == $past(assertion))
    );

    // A start_event from idle arms the timer and sets active.
    check_idle_start_arms_timer: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && !active && start_event)
        |=> (timer == 32'd0) &&
            (active == 1'b1) &&
            (assertion == $past(assertion))
    );

    // Idle state holds on a terminal count without start_event.
    check_idle_without_start_holds_state: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && !active && !start_event)
        |=> (timer == $past(timer)) &&
            (active == 1'b0) &&
            (assertion == $past(assertion))
    );

    // While active, the timer increments before the window is reached.
    check_active_increments_before_window: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && !start_event && (timer < window))
        |=> (timer == ($past(timer) + 32'd1)) &&
            (active == 1'b1) &&
            (assertion == $past(assertion))
    );

    // While active, reaching the window updates assertion and clears active.
    check_active_completes_at_window: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && !start_event && (timer >= window))
        |=> (timer == ($past(timer) + 32'd1)) &&
            (active == 1'b0) &&
            (assertion == $past(test_expr))
    );

    // A non-ignored new start while active rearms the timer.
    check_new_start_rearms_timer: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && !ignore_new_start)
        |=> (timer == 32'd0) &&
            (active == 1'b1)
    );

    // A non-ignored new start can clear assertion when either clear flag is set.
    check_new_start_clears_assertion: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && !ignore_new_start &&
         (reset_on_new_start || error_on_new_start))
        |=> (assertion == 1'b0)
    );

    // A non-ignored new start without clear flags keeps assertion before expiry.
    check_new_start_keeps_assertion_before_window: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && !ignore_new_start &&
         !reset_on_new_start && !error_on_new_start && (timer < window))
        |=> (assertion == $past(assertion))
    );

    // A non-ignored new start without clear flags still samples test_expr at expiry.
    check_new_start_updates_assertion_at_window: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && !ignore_new_start &&
         !reset_on_new_start && !error_on_new_start && (timer >= window))
        |=> (assertion == $past(test_expr))
    );

    // An ignored new start does not reset the timer before expiry.
    check_ignored_new_start_does_not_restart_before_window: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && ignore_new_start &&
         (timer < window))
        |=> (timer == ($past(timer) + 32'd1)) &&
            (active == 1'b1) &&
            (assertion == $past(assertion))
    );

    // An ignored new start does not block completion at or beyond the window.
    check_ignored_new_start_allows_completion: assert property (
        @(posedge clk) disable iff (!reset_n)
        (num_cks_counter == num_cks && active && start_event && ignore_new_start &&
         (timer >= window))
        |=> (timer == ($past(timer) + 32'd1)) &&
            (active == 1'b0) &&
            (assertion == $past(test_expr))
    );

endmodule