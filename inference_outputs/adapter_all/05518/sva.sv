module reset_sync_sva #(
    parameter int RESET_SYNC_STAGES = 4,
    parameter int NUM_RESET_OUTPUT  = 1
) (
    input logic reset_n,
    input logic clk,
    input logic [NUM_RESET_OUTPUT-1:0] reset_n_sync
);

    // Clock: clk
    // Reset: reset_n active-low, asynchronous
    // Logic: mixed sequential/combinational; reset_n_sync is a registered output

    // reset_n_sync is low whenever reset_n is low.
    check_reset_low_forces_sync_low: assert property (
        @(posedge clk) !reset_n |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // reset_n_sync is high whenever reset_n is high.
    check_reset_high_forces_sync_high: assert property (
        @(posedge clk) reset_n |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // A sampled reset deassertion must be reflected on reset_n_sync by the next clock.
    check_reset_release_propagates: assert property (
        @(posedge clk) $rose(reset_n) |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // A sampled reset assertion must be reflected on reset_n_sync by the next clock.
    check_reset_assert_propagates: assert property (
        @(posedge clk) $fell(reset_n) |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // reset_n_sync can only change when reset_n itself changes.
    check_sync_change_requires_reset_change: assert property (
        @(posedge clk) $changed(reset_n_sync) |-> $changed(reset_n)
    );

    // reset_n_sync can only change when reset_n itself changes.
    check_sync_change_requires_reset_change_2: assert property (
        @(posedge clk) $changed(reset_n_sync) |-> $changed(reset_n)
    );

    // If reset_n is high, reset_n_sync must be high on the next clock.
    check_sync_high_when_reset_high: assert property (
        @(posedge clk) reset_n |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // If reset_n is low, reset_n_sync must be low on the next clock.
    check_sync_low_when_reset_low: assert property (
        @(posedge clk) !reset_n |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // A sampled reset deassertion must be reflected on reset_n_sync by the next clock.
    check_reset_release_propagates_2: assert property (
        @(posedge clk) $rose(reset_n) |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // A sampled reset assertion must be reflected on reset_n_sync by the next clock.
    check_reset_assert_propagates_2: assert property (
        @(posedge clk) $fell(reset_n) |-> ##1 (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

endmodule