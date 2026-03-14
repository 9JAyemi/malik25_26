module reg_16bit_sva (
    input logic clk,
    input logic Load,
    input logic not_reset, // active-low async reset
    input logic [15:0] D,
    input logic [15:0] Q
);
    // Reset low drives Q to zero in the same cycle.
    check_reset_clears_q_now: assert property (
        @(posedge clk) !not_reset |-> (Q == 16'h0000)
    );

    // After any cycle with reset low, Q is zero on the next cycle.
    check_zero_one_cycle_after_reset: assert property (
        @(posedge clk) (!not_reset) |=> (Q == 16'h0000)
    );

    // With Load high, next cycle Q equals sampled D or becomes zero if an async reset occurred.
    check_load_captures_d_or_zero_next: assert property (
        @(posedge clk) disable iff (!not_reset)
            (Load) |=> ((Q == $past(D)) || (Q == 16'h0000))
    );

    // With Load low, next cycle Q holds or becomes zero if an async reset occurred.
    check_hold_or_zero_next: assert property (
        @(posedge clk) disable iff (!not_reset)
            (!Load) |=> ($stable(Q) || (Q == 16'h0000))
    );

    // If no Load, any observed Q change by next cycle must be a reset to zero.
    check_change_without_load_means_zero: assert property (
        @(posedge clk) disable iff (!not_reset)
            (!Load) |=> (!$changed(Q) || (Q == 16'h0000))
    );

    // Loading D==0 guarantees Q==0 on the next cycle (or remains 0 under reset).
    check_load_zero_data_results_zero: assert property (
        @(posedge clk) disable iff (!not_reset)
            (Load && (D == 16'h0000)) |=> (Q == 16'h0000)
    );

    // Reset has priority over Load when asserted.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (!not_reset && Load) |-> (Q == 16'h0000)
    );

    // If Q rises from zero to nonzero, the prior cycle must have had Load asserted.
    check_nonzero_rise_requires_prior_load: assert property (
        @(posedge clk) disable iff (!not_reset)
            (Q == 16'h0000) |=> ((Q != 16'h0000) -> $past(Load))
    );

    // If a nonzero value is observed after a Load with nonzero D, it must equal the sampled D.
    check_nonzero_after_load_matches_d: assert property (
        @(posedge clk) disable iff (!not_reset)
            (Load && (D != 16'h0000)) |=> ((Q != 16'h0000) -> (Q == $past(D)))
    );

    // With no Load, a nonzero Q remains unchanged into the next cycle unless reset forces it to zero.
    check_hold_preserves_nonzero: assert property (
        @(posedge clk) disable iff (!not_reset)
            (!Load) |=> (((Q != 16'h0000) && ($past(Q) != 16'h0000)) -> (Q == $past(Q)))
    );
endmodule