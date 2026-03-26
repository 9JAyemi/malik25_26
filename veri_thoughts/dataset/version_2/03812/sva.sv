module t_ff_pipeline_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q equals prior q XOR d delayed by three sampled clocks.
    check_q_matches_three_cycle_delayed_xor: assert property (
        @(posedge clk) $past(1'b1,3) |-> (q == ($past(q) ^ $past(d,3)))
    );

    // A delayed high d sample toggles q.
    check_q_toggles_on_delayed_high_d: assert property (
        @(posedge clk) ($past(1'b1,3) && $past(d,3)) |-> (q != $past(q))
    );

    // A delayed low d sample leaves q unchanged.
    check_q_holds_on_delayed_low_d: assert property (
        @(posedge clk) ($past(1'b1,3) && !$past(d,3)) |-> (q == $past(q))
    );

endmodule