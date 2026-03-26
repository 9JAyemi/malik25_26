module debouncer_assertions #(
    parameter clk_freq = 100000000,
    parameter debounce_time = 50
) (
    input logic        clk,
    input logic        in,
    input logic        out,
    input logic [31:0] count,
    input logic [31:0] debounce_cycles
);

    // On a mismatch, count is reset on the next clock.
    check_count_reset_on_mismatch: assert property (
        @(posedge clk)
        (in != out) |=> (count == 32'd0)
    );

    // On a mismatch, debounce_cycles is reloaded from the parameter expression.
    check_debounce_cycles_reload_on_mismatch: assert property (
        @(posedge clk)
        (in != out) |=> (debounce_cycles == (debounce_time * clk_freq / 1000))
    );

    // On a mismatch, out is not assigned and must hold its value.
    check_out_hold_on_mismatch: assert property (
        @(posedge clk)
        (in != out) |=> (out == $past(out))
    );

    // While input matches output and count is below the threshold, count increments.
    check_count_increment_while_matched_below_threshold: assert property (
        @(posedge clk)
        (in == out && count < debounce_cycles) |=> (count == ($past(count) + 32'd1))
    );

    // While input matches output and count is below the threshold, debounce_cycles holds.
    check_debounce_cycles_hold_while_matched_below_threshold: assert property (
        @(posedge clk)
        (in == out && count < debounce_cycles) |=> (debounce_cycles == $past(debounce_cycles))
    );

    // While input matches output and count is below the threshold, out holds.
    check_out_hold_while_matched_below_threshold: assert property (
        @(posedge clk)
        (in == out && count < debounce_cycles) |=> (out == $past(out))
    );

    // Once count reaches the threshold with input matching output, count holds.
    check_count_hold_while_matched_at_threshold: assert property (
        @(posedge clk)
        (in == out && count >= debounce_cycles) |=> (count == $past(count))
    );

    // Once count reaches the threshold with input matching output, debounce_cycles holds.
    check_debounce_cycles_hold_while_matched_at_threshold: assert property (
        @(posedge clk)
        (in == out && count >= debounce_cycles) |=> (debounce_cycles == $past(debounce_cycles))
    );

    // Once count reaches the threshold with input matching output, out is assigned from in.
    check_out_update_while_matched_at_threshold: assert property (
        @(posedge clk)
        (in == out && count >= debounce_cycles) |=> (out == $past(in))
    );

endmodule