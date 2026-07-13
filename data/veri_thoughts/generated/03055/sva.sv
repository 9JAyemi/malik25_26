module input_pulse_toggle_sva (
    input logic clk,
    input logic in,
    input logic reset,
    input logic out
);

    // Active-low reset drives the output low.
    check_reset_forces_out_low: assert property (
        @(posedge clk) !$initstate && !reset |-> (out == 1'b0)
    );

    // First active cycle after reset with low input keeps output low.
    check_post_reset_low_input_keeps_out_low: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && !$past(reset) && !in) |=> (out == 1'b0)
    );

    // First active cycle after reset with high input sets output high.
    check_post_reset_high_input_sets_out_high: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && !$past(reset) && in) |=> (out == 1'b1)
    );

    // A sampled 0-to-1 input transition toggles the output.
    check_sampled_rise_toggles_out: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $past(reset) && in && !$past(in)) |=> (out == ~$past(out))
    );

    // Low input on an active cycle leaves the output unchanged.
    check_low_input_holds_out: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $past(reset) && !in) |=> (out == $past(out))
    );

    // High input held across active cycles leaves the output unchanged.
    check_steady_high_holds_out: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $past(reset) && in && $past(in)) |=> (out == $past(out))
    );

endmodule