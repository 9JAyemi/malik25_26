module reset_sync_sva #(
    parameter int RESET_SYNC_STAGES = 4,
    parameter int NUM_RESET_OUTPUT  = 1
) (
    input logic reset_n,
    input logic clk,
    input logic [NUM_RESET_OUTPUT-1:0] reset_n_sync
);

    // reset_n_sync must be low whenever reset_n is low.
    check_sync_low_during_reset: assert property (
        @(posedge clk) !reset_n |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // reset_n_sync must be high whenever reset_n is high.
    check_sync_high_during_active: assert property (
        @(posedge clk) reset_n |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // A sampled reset deassertion must leave reset_n_sync low on the next clock.
    check_sync_low_after_reset_release: assert property (
        @(posedge clk) $rose(reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b0}})
    );

    // A sampled reset assertion must leave reset_n_sync high on the next clock.
    check_sync_high_after_reset_assert: assert property (
        @(posedge clk) $fell(reset_n) |-> (reset_n_sync == {NUM_RESET_OUTPUT{1'b1}})
    );

    // reset_n_sync must remain stable while reset_n is held low.
    check_sync_stable_during_reset: assert property (
        @(posedge clk) (!reset_n && $past(!reset_n)) |-> (reset_n_sync == $past(reset_n_sync))
    );

    // reset_n_sync must remain stable while reset_n is held high.
    check_sync_stable_during_active: assert property (
        @(posedge clk) (reset_n && $past(reset_n)) |-> (reset_n_sync == $past(reset_n_sync))
    );

endmodule