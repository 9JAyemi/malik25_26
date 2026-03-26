module altera_std_synchronizer_sva #(
    parameter int depth = 2
) (
    input  logic             clk,
    input  logic             reset_n,
    input  logic             din,
    input  logic             dout,
    input  logic [depth-1:0] ff
);

    // Reset clears all synchronizer stages.
    check_reset_clears_ff: assert property (
        @(posedge clk) !reset_n |-> (ff == {depth{1'b0}})
    );

    // Reset drives the synchronized output low.
    check_reset_clears_dout: assert property (
        @(posedge clk) !reset_n |-> (dout == 1'b0)
    );

    // The output is the last stage of the synchronizer chain.
    check_dout_matches_last_stage: assert property (
        @(posedge clk) disable iff (!reset_n) (dout == ff[depth-1])
    );

    // A sampled reset keeps all stages at zero on the next sampled cycle.
    check_reset_holds_zero_ff_to_next_cycle: assert property (
        @(posedge clk) !reset_n |=> (ff == {depth{1'b0}})
    );

    // A sampled reset keeps the output low on the next sampled cycle.
    check_reset_holds_zero_dout_to_next_cycle: assert property (
        @(posedge clk) !reset_n |=> (dout == 1'b0)
    );

    // On the sampled release of reset, the state still starts from zero.
    check_release_starts_from_zero_ff: assert property (
        @(posedge clk) disable iff (!reset_n) $rose(reset_n) |-> (ff == {depth{1'b0}})
    );

    // On the sampled release of reset, the output still starts low.
    check_release_starts_from_zero_dout: assert property (
        @(posedge clk) disable iff (!reset_n) $rose(reset_n) |-> (dout == 1'b0)
    );

endmodule