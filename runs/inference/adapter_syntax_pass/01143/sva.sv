module dual_edge_triggered_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q is high on the first sampled negedge after a high d.
    check_q_high_after_high_d: assert property (
        @(negedge clk) disable iff ($initstate)
        ($past(d) == 1'b1) |-> (q == 1'b1)
    );

    // q is low on the first sampled negedge after a low d.
    check_q_low_after_low_d: assert property (
        @(negedge clk) disable iff ($initstate)
        ($past(d) == 1'b0) |-> (q == 1'b0)
    );

    // q is high on the second sampled negedge after a high d.
    check_q_high_after_second_high_d: assert property (
        @(negedge clk) disable iff ($initstate)
        (($past(d) == 1'b1) && ($past(q) == 1'b1)) |-> (q == 1'b1)
    );

    // q is low on the second sampled negedge after a low d.
    check_q_low_after_second_low_d: assert property (
        @(negedge clk) disable iff ($initstate)
        (($past(d) == 1'b0) && ($past(q) == 1'b0)) |-> (q == 1'b0)
    );

endmodule