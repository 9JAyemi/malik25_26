module uut_sva (
    input  logic       clk,
    input  logic       d,
    input  logic       r,
    input  logic       e,
    input  logic [2:0] q
);
    ///// q0 (synchronous to clk, active-high sync reset via r) /////
    // q0 becomes 0 on the cycle after r is HIGH (synchronous reset).
    check_q0_sync_reset_next: assert property (
        @(posedge clk) r |=> (q[0] == 1'b0)
    );

    // When !r and e, q0 captures d on the next cycle.
    check_q0_load_on_e: assert property (
        @(posedge clk) disable iff ($initstate || r) (!r && e) |=> (q[0] == $past(d))
    );

    // When !r and !e, q0 holds its value to the next cycle.
    check_q0_hold_when_no_e: assert property (
        @(posedge clk) disable iff ($initstate || r) (!r && !e) |=> (q[0] == $past(q[0]))
    );

    // q0 can only change if prior cycle had r HIGH or e HIGH.
    check_q0_change_gated_by_e_or_r: assert property (
        @(posedge clk) disable iff ($initstate) $changed(q[0]) |-> ($past(r) || $past(e))
    );

    // If !r and e and d equals current q0, q0 does not change next cycle.
    check_q0_write_same_no_change: assert property (
        @(posedge clk) disable iff ($initstate || r) (!r && e && (d == q[0])) |=> (q[0] == $past(q[0]))
    );

    // If !r and e and d differs from current q0, q0 changes next cycle.
    check_q0_write_diff_changes: assert property (
        @(posedge clk) disable iff ($initstate || r) (!r && e && (d != q[0])) |=> (q[0] != $past(q[0]))
    );

    ///// q1 (clocked by clk with async active-high reset r) /////
    // While r is HIGH at the clock edge, q1 must be 0 (async reset level).
    check_q1_async_reset_level: assert property (
        @(posedge clk) r |-> (q[1] == 1'b0)
    );

    // One cycle after r was HIGH, q1 is still 0.
    check_q1_post_reset_zero: assert property (
        @(posedge clk) disable iff ($initstate) $past(r) |-> (q[1] == 1'b0)
    );

    ///// q2 (clocked by clk with async active-low reset r) /////
    // While r is LOW at the clock edge, q2 must be 0 (async reset level).
    check_q2_async_reset_level: assert property (
        @(posedge clk) !r |-> (q[2] == 1'b0)
    );

    // One cycle after r was LOW, q2 is still 0.
    check_q2_post_reset_zero: assert property (
        @(posedge clk) disable iff ($initstate) $past(!r) |-> (q[2] == 1'b0)
    );

endmodule