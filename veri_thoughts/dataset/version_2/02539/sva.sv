module d_flip_flop_sva (
    input logic D,
    input logic CLK,
    input logic Q
);

    // Q equals D from the previous rising CLK edge (1-cycle latency).
    check_q_follows_prev_d: assert property (
        @(posedge CLK) Q == $past(D)
    );

    // If D changed between the last two edges, Q changes on this edge.
    check_q_changes_when_d_changed_last_cycle: assert property (
        @(posedge CLK) ($past(D) != $past(D,2)) |-> (Q != $past(Q))
    );

    // If D was the same on the last two edges, Q is stable on this edge.
    check_q_stable_when_d_stable_last_cycle: assert property (
        @(posedge CLK) ($past(D) == $past(D,2)) |-> (Q == $past(Q))
    );

    // If D is 1 on this edge, Q will be 1 on the next edge.
    check_next_q_high_when_d_high: assert property (
        @(posedge CLK) (D == 1'b1) |-> ##1 (Q == 1'b1)
    );

    // If D is 0 on this edge, Q will be 0 on the next edge.
    check_next_q_low_when_d_low: assert property (
        @(posedge CLK) (D == 1'b0) |-> ##1 (Q == 1'b0)
    );

endmodule