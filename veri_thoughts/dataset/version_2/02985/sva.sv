module t_flip_flop_sva (
    input logic clk,
    input logic t,
    input logic q
);
    // Analysis: clock=clk (posedge), no reset; sequential TFF with q_next = q ^ t.

    // q updates to previous q XOR previous t each rising edge.
    check_next_state_function: assert property (
        @(posedge clk) disable iff ($initstate) q == ($past(q) ^ $past(t))
    );

    // When previous t is 0, q holds its value.
    check_hold_when_t0: assert property (
        @(posedge clk) disable iff ($initstate) ($past(t) == 1'b0) |-> (q == $past(q))
    );

    // When previous t is 1, q toggles.
    check_toggle_when_t1: assert property (
        @(posedge clk) disable iff ($initstate) ($past(t) == 1'b1) |-> (q != $past(q))
    );

    // Any change in q implies previous t was 1.
    check_change_implies_t1: assert property (
        @(posedge clk) disable iff ($initstate) (q != $past(q)) |-> ($past(t) == 1'b1)
    );
endmodule