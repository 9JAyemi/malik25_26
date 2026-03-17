module altera_tse_false_path_marker_sva
#(
    parameter MARKER_WIDTH = 1
)
(
    input logic reset,
    input logic clk,
    input logic [MARKER_WIDTH - 1 : 0] data_in,
    input logic [MARKER_WIDTH - 1 : 0] data_out
);

    localparam logic [MARKER_WIDTH - 1 : 0] ZERO = {MARKER_WIDTH{1'b0}};

    // Reset forces the registered output low.
    check_reset_drives_zero: assert property (
        @(posedge clk) reset |-> (data_out == ZERO)
    );

    // A sampled reset keeps the output low until the next clock edge.
    check_reset_keeps_zero_next_cycle: assert property (
        @(posedge clk) reset |=> (data_out == ZERO)
    );

    // Outside reset, the sampled output is either zero or the prior sampled input.
    check_output_is_zero_or_prior_input: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset, 1, 1'b1) |-> ((data_out == ZERO) || (data_out == $past(data_in, 1, ZERO)))
    );

    // Any nonzero sampled output must match the prior sampled input.
    check_nonzero_output_matches_prior_input: assert property (
        @(posedge clk) disable iff (reset)
        (data_out != ZERO) && !$past(reset, 1, 1'b1) |-> (data_out == $past(data_in, 1, ZERO))
    );

    // A nonzero output is never observed while reset is sampled high.
    check_nonzero_output_not_during_reset: assert property (
        @(posedge clk) (data_out != ZERO) |-> !reset
    );

endmodule