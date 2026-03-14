module top_module_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // q equals D sampled on previous rising edge.
    check_q_captures_prev_d: assert property (
        @(posedge clk) $past(1'b1) |-> (q == $past(d))
    );

    // If q changed this cycle, D changed one cycle earlier.
    check_q_change_implies_prev_d_change: assert property (
        @(posedge clk) $past(1'b1,2) |-> ($changed(q) |-> ($past(d) != $past(d,2)))
    );

    // If D changed one cycle earlier, q changes this cycle.
    check_prev_d_change_implies_q_change: assert property (
        @(posedge clk) $past(1'b1,2) |-> (($past(d) != $past(d,2)) |-> $changed(q))
    );

    // If D was stable over the prior two cycles, q is stable this cycle.
    check_stable_d_implies_stable_q: assert property (
        @(posedge clk) $past(1'b1,2) |-> (($past(d) == $past(d,2)) |-> (q == $past(q)))
    );
endmodule

module jk_flip_flop_sva (
    input logic clk,
    input logic j,
    input logic k,
    input logic q
);
    // J=1,K=0 sets q to 1 on the next sample.
    jk_set: assert property (
        @(posedge clk) (j && ~k) |=> (q == 1'b1)
    );

    // J=0,K=1 resets q to 0 on the next sample.
    jk_reset: assert property (
        @(posedge clk) (~j && k) |=> (q == 1'b0)
    );

    // J=1,K=1 toggles q on the next sample.
    jk_toggle: assert property (
        @(posedge clk) (j && k) |=> (q == ~ $past(q))
    );

    // J=0,K=0 holds q on the next sample.
    jk_hold: assert property (
        @(posedge clk) (~j && ~k) |=> (q == $past(q))
    );
endmodule