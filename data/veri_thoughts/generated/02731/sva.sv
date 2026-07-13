module d_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // q equals previous cycle's d
    dff_q_eq_past_d: assert property (
        @(posedge clk) q == $past(d)
    );

    // If d changed since last cycle, q reflects previous d and not current d
    dff_d_change_implication: assert property (
        @(posedge clk) $changed(d) |-> (q == $past(d)) && (q != d)
    );

    // If d did not change since last cycle, q equals current d
    dff_d_nochange_eq_current: assert property (
        @(posedge clk) !$changed(d) |-> (q == d)
    );

    // If q changed since last cycle, then d changed in the prior cycle
    dff_q_change_implies_prior_d_change: assert property (
        @(posedge clk) $changed(q) |-> ($past(d) != $past(d,2))
    );

    // If d changed in the prior cycle, q changes this cycle
    dff_prior_d_change_implies_q_change: assert property (
        @(posedge clk) ($past(d) != $past(d,2)) |-> $changed(q)
    );
endmodule