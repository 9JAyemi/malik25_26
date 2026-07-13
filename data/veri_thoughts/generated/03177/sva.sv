module synchronous_reset_sva (
    input logic clk,
    input logic out,
    input logic in0,
    input logic AS
);

    // Active-low reset forces AS low at sampled clocks.
    check_reset_forces_as_low: assert property (
        @(posedge clk) disable iff ($initstate) !in0 |-> (AS == 1'b0)
    );

    // A reset-active sampled cycle leaves AS low on the next sampled clock.
    check_reset_cycle_keeps_as_low: assert property (
        @(posedge clk) disable iff ($initstate) $past(!in0) |-> (AS == 1'b0)
    );

    // With reset inactive, a prior low out must produce a low AS.
    check_low_out_captures_low: assert property (
        @(posedge clk) disable iff (!in0 || $initstate) $past(in0 && !out) |-> (AS == 1'b0)
    );

    // A high AS must come from a prior clock with reset inactive and out high.
    check_high_as_requires_prior_high_out: assert property (
        @(posedge clk) disable iff (!in0 || $initstate) AS |-> $past(in0 && out)
    );

endmodule