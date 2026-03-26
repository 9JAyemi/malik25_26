module dual_edge_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // A sampled 0-to-1 transition on d makes q high on the next clock.
    check_sampled_rise_sets_q_next: assert property (
        @(posedge clk)
        (!$isunknown($past(d,1)) && ($past(d,1) == 1'b0) && (d == 1'b1)) |=> (q == 1'b1)
    );

    // Any non-rising sampled d pattern keeps q low on the next clock.
    check_non_rise_clears_q_next: assert property (
        @(posedge clk)
        (!$isunknown($past(d,1)) && !(($past(d,1) == 1'b0) && (d == 1'b1))) |=> (q == 1'b0)
    );

    // q does not assert in the same cycle that d is sampled rising.
    check_rise_detect_is_delayed: assert property (
        @(posedge clk)
        (!$isunknown($past(d,1)) && ($past(d,1) == 1'b0) && (d == 1'b1)) |-> (q == 1'b0)
    );

    // q can only be high after the two previous d samples were 0 then 1.
    check_q_high_only_after_sampled_rise: assert property (
        @(posedge clk)
        (!$isunknown($past(d,2)) && (q == 1'b1)) |-> (($past(d,2) == 1'b0) && ($past(d,1) == 1'b1))
    );

    // q is a one-cycle pulse once enough input history exists.
    check_q_is_single_cycle_pulse: assert property (
        @(posedge clk)
        (!$isunknown($past(d,2)) && (q == 1'b1)) |=> (q == 1'b0)
    );

    // q matches the delayed rise-detect function of sampled d.
    check_q_matches_delayed_rise_detect: assert property (
        @(posedge clk)
        !$isunknown($past(d,2)) |-> (q == ($past(d,1) & (~$past(d,2))))
    );

endmodule