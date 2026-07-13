module altera_tse_false_path_marker_sva 
#(
    parameter int MARKER_WIDTH = 1
)
(
    input  logic                      reset,
    input  logic                      clk,
    input  logic [MARKER_WIDTH-1:0]   data_in,
    input  logic [MARKER_WIDTH-1:0]   data_out
);

    // If reset is HIGH, output must be zero on the next cycle.
    check_output_zero_next_after_reset: assert property (
        @(posedge clk) reset |=> (data_out == {MARKER_WIDTH{1'b0}})
    );

    // If the previous cycle had reset HIGH, output must be zero now.
    check_output_zero_if_prev_cycle_reset: assert property (
        @(posedge clk) $past(reset) |-> (data_out == {MARKER_WIDTH{1'b0}})
    );

    // On a sampled falling edge of reset, output is zero on that cycle.
    check_output_zero_on_reset_fall_now: assert property (
        @(posedge clk) $fell(reset) |-> (data_out == {MARKER_WIDTH{1'b0}})
    );

    // With reset LOW on consecutive samples, output is either previous input or zero.
    check_prev_in_or_zero_when_no_reset_sampled: assert property (
        @(posedge clk) disable iff (reset)
            (!reset && !$past(reset)) |-> ((data_out == $past(data_in)) || (data_out == {MARKER_WIDTH{1'b0}}))
    );

    // With reset LOW on consecutive samples, a non-zero output must equal previous input.
    check_nonzero_output_matches_prev_input_when_no_reset_sampled: assert property (
        @(posedge clk) disable iff (reset)
            (!reset && !$past(reset) && (data_out != {MARKER_WIDTH{1'b0}})) |-> (data_out == $past(data_in))
    );

    // Output is never X/Z while reset is HIGH.
    check_output_not_unknown_during_reset: assert property (
        @(posedge clk) reset |-> !$isunknown(data_out)
    );

endmodule