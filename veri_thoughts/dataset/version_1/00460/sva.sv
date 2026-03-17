module pulse_detection_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic [15:0] threshold,
    input logic [15:0] frequency,
    input logic        threshold_exceeded,
    input logic [31:0] count,
    input logic [3:0]  prescaler,
    input logic [31:0] prev_in,
    input logic [31:0] curr_in
);

    // Reset clears all state and outputs.
    reset_clears_state: assert property (
        @(posedge clk)
        reset |-> (count == 32'd0) &&
                  (prescaler == 4'd0) &&
                  (prev_in == 32'd0) &&
                  (curr_in == 32'd0) &&
                  (frequency == 16'd0) &&
                  (threshold_exceeded == 1'b0)
    );

    // A zero prescaler reloads to 15 on the next cycle.
    prescaler_reloads_after_sample: assert property (
        @(posedge clk) disable iff (reset)
        (prescaler == 4'd0) |=> (prescaler == 4'd15)
    );

    // A nonzero prescaler decrements by one each cycle.
    prescaler_decrements_while_busy: assert property (
        @(posedge clk) disable iff (reset)
        (prescaler != 4'd0) |=> (prescaler == ($past(prescaler) - 4'd1))
    );

    // Sampling updates prev_in from curr_in and curr_in from in.
    sample_updates_input_history: assert property (
        @(posedge clk) disable iff (reset)
        (prescaler == 4'd0) |=> (prev_in == $past(curr_in)) &&
                                (curr_in == $past(in))
    );

    // Without sampling, prev_in and curr_in hold their values.
    hold_input_history_while_prescaling: assert property (
        @(posedge clk) disable iff (reset)
        (prescaler != 4'd0) |=> (prev_in == $past(prev_in)) &&
                                (curr_in == $past(curr_in))
    );

    // An exact sampled 0-to-1 value increments count below the window limit.
    count_increments_on_qualified_sample: assert property (
        @(posedge clk) disable iff (reset)
        (prescaler == 4'd0) &&
        (prev_in == 32'd0) &&
        (curr_in == 32'd1) &&
        (count < 32'd100000000)
        |=> (count == ($past(count) + 32'd1))
    );

    // Without a qualified sample, count holds below the window limit.
    count_holds_without_qualified_sample: assert property (
        @(posedge clk) disable iff (reset)
        (count < 32'd100000000) &&
        !((prescaler == 4'd0) && (prev_in == 32'd0) && (curr_in == 32'd1))
        |=> (count == $past(count))
    );

    // Reaching the window limit clears count on the next cycle.
    count_clears_at_window_end: assert property (
        @(posedge clk) disable iff (reset)
        (count >= 32'd100000000) |=> (count == 32'd0)
    );

    // Reaching the window limit updates frequency from count / 100000.
    frequency_updates_at_window_end: assert property (
        @(posedge clk) disable iff (reset)
        (count >= 32'd100000000) |=> (frequency == ($past(count) / 32'd100000))
    );

    // Before the window ends, frequency holds its value.
    frequency_holds_before_window_end: assert property (
        @(posedge clk) disable iff (reset)
        (count < 32'd100000000) |=> (frequency == $past(frequency))
    );

    // Reaching the window limit updates the flag from the prior frequency comparison.
    threshold_flag_updates_at_window_end: assert property (
        @(posedge clk) disable iff (reset)
        (count >= 32'd100000000)
        |=> (threshold_exceeded == ($past(frequency) > $past(threshold)))
    );

    // Before the window ends, the threshold flag holds its value.
    threshold_flag_holds_before_window_end: assert property (
        @(posedge clk) disable iff (reset)
        (count < 32'd100000000) |=> (threshold_exceeded == $past(threshold_exceeded))
    );

endmodule