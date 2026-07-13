module dual_toggle_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic in,
    input logic out,
    input logic q1,
    input logic q2
);

    // Sampled low reset clears both flops and the output.
    check_reset_clears_state: assert property (
        @(posedge clk) !reset |-> (q1 == 1'b0) && (q2 == 1'b0) && (out == 1'b0)
    );

    // The reset release edge is sampled before the first active-clock update.
    check_release_cycle_samples_cleared_state: assert property (
        @(posedge clk) $rose(reset) |-> (q1 == 1'b0) && (q2 == 1'b0) && (out == 1'b0)
    );

    // q1 toggles on each active clock after a prior active cycle.
    check_q1_toggles_each_active_cycle: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $past(reset) |-> (q1 == ~$past(q1))
    );

    // q2 toggles on each active clock after a prior active cycle.
    check_q2_toggles_each_active_cycle: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $past(reset) |-> (q2 == ~$past(q2))
    );

    // out equals the previous cycle XOR of q1 and q2.
    check_out_matches_previous_xor: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $past(reset) |-> (out == ($past(q1) ^ $past(q2)))
    );

    // Once q1 and q2 are equal, they stay equal and keep out low.
    check_equal_state_preserved_and_out_low: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(reset) && ($past(q1) == $past(q2))) |-> ((q1 == q2) && (out == 1'b0))
    );

    // One active cycle after reset release, both flops are high and out is low.
    check_first_active_cycle_after_reset: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        $rose(reset) |=> (q1 == 1'b1) && (q2 == 1'b1) && (out == 1'b0)
    );

endmodule

bind dual_toggle_flip_flop dual_toggle_flip_flop_sva dual_toggle_flip_flop_sva_i (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .q1(q1),
    .q2(q2)
);