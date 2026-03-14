module top_module_sva (
    input logic clk,
    input logic rst,
    input logic sel,
    input logic [3:0] q
);

    ///// Reset behavior /////
    // On asserting rst, q becomes 0 on the next clock.
    reset_next_sets_q_zero: assert property (
        @(posedge clk) rst |=> (q == 4'b0000)
    );

    // While rst stays asserted across cycles, q remains 0.
    hold_q_zero_during_rst: assert property (
        @(posedge clk) rst && $past(rst) |-> (q == 4'b0000)
    );

    // On deasserting rst (high->low), q is still 0 in that cycle.
    q_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (q == 4'b0000)
    );

    ///// q update rules relative to previous cycle /////
    // If sel was 1 last cycle (and not in reset), q increments by 1 modulo 16.
    q_increments_when_sel_prev: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(sel) |-> (q == ($past(q) + 4'd1))
    );

    // If sel was 0 last cycle (and not in reset), q holds its value.
    q_holds_when_no_sel_prev: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && !$past(sel) |-> (q == $past(q))
    );

    // Any change in q must be caused by previous sel or previous rst.
    q_change_has_valid_cause: assert property (
        @(posedge clk) disable iff (rst)
            $changed(q) |-> ($past(sel) || $past(rst))
    );

    // When q was 4'hF and sel was 1 last cycle (not in reset), q wraps to 0.
    q_wraps_on_max_when_sel_prev: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) && $past(sel) && ($past(q) == 4'hF) |-> (q == 4'h0)
    );

    // A rising sel has no immediate (same-cycle) effect on q.
    no_immediate_change_on_sel_rise: assert property (
        @(posedge clk) disable iff (rst)
            $rose(sel) && $past(!rst) |-> (q == $past(q))
    );

endmodule