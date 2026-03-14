module dut_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] input_signal,
    input logic [3:0] output_signal,
    input logic [3:0] count
);
    // Synchronous reset drives count and output_signal to 0 in the next cycle.
    check_reset_clears_both: assert property (
        @(posedge clk) reset |=> (count == 4'd0) && (output_signal == 4'd0)
    );

    // All-zeros or all-ones input drives both count and output to 0 next cycle.
    check_sentinel_clears_both: assert property (
        @(posedge clk) disable iff (reset)
            ((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) |=> (count == 4'd0) && (output_signal == 4'd0)
    );

    // With MSB=1 (and not sentinel), count becomes 1 next cycle.
    check_msb1_sets_count_one: assert property (
        @(posedge clk) disable iff (reset)
            (!((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) && (input_signal[15] == 1'b1)) |=> (count == 4'd1)
    );

    // With MSB=1 (and not sentinel), output becomes previous count next cycle.
    check_msb1_updates_output_prev_count: assert property (
        @(posedge clk) disable iff (reset)
            (!((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) && (input_signal[15] == 1'b1) && $past(!reset)) |=> (output_signal == $past(count))
    );

    // With MSB=0 (and not sentinel), count increments by 1 modulo 16 next cycle.
    check_msb0_increments_count: assert property (
        @(posedge clk) disable iff (reset)
            (!((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) && (input_signal[15] == 1'b0) && $past(!reset)) |=> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1)))
    );

    // With MSB=0 (and not sentinel), output holds its previous value next cycle.
    check_msb0_holds_output: assert property (
        @(posedge clk) disable iff (reset)
            (!((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) && (input_signal[15] == 1'b0) && $past(!reset)) |=> (output_signal == $past(output_signal))
    );

    // Output can change only if prior cycle was reset, sentinel, or MSB=1.
    check_output_changes_only_when_driven: assert property (
        @(posedge clk) disable iff (reset)
            $changed(output_signal) |-> ($past(reset) || $past((input_signal == 16'hFFFF) || (input_signal == 16'h0000) || (input_signal[15] == 1'b1)))
    );

    // Count wraps from 15 to 0 when incrementing under MSB=0.
    check_increment_wraps_at_15: assert property (
        @(posedge clk) disable iff (reset)
            (!((input_signal == 16'hFFFF) || (input_signal == 16'h0000)) && (input_signal[15] == 1'b0) && $past(!reset) && ($past(count) == 4'hF)) |=> (count == 4'h0)
    );
endmodule