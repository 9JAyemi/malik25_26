module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [15:0] q
);
    // Reset drives q to zero (synchronous, active-high).
    reset_sets_zero: assert property (
        @(posedge clk) reset |-> (q == 16'd0)
    );

    // When load is asserted, q holds its previous value (load path is identity).
    hold_on_load: assert property (
        @(posedge clk) disable iff (reset) load |=> (q == $past(q))
    );

    // When not loading and up_down=1, next q increments by 1.
    count_up_when_up: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |=> (q == $past(q) + 16'd1)
    );

    // When not loading and up_down=0, next q decrements by 1.
    count_down_when_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |=> (q == $past(q) - 16'd1)
    );

    // If q changed from last cycle, load must have been deasserted.
    change_implies_no_load: assert property (
        @(posedge clk) disable iff (reset) (q != $past(q)) |-> (!$past(load))
    );

    // If q stayed the same (no reset), load must have been asserted.
    stable_implies_load: assert property (
        @(posedge clk) disable iff (reset) (q == $past(q)) |-> ($past(load))
    );

    // If q incremented, the previous cycle was up count without load.
    inc_implies_up_no_load: assert property (
        @(posedge clk) disable iff (reset) (q == $past(q) + 16'd1) |-> (!$past(load) && $past(up_down))
    );

    // If q decremented, the previous cycle was down count without load.
    dec_implies_down_no_load: assert property (
        @(posedge clk) disable iff (reset) (q == $past(q) - 16'd1) |-> (!$past(load) && !$past(up_down))
    );

    // Load has priority over up_down when both are asserted (q holds).
    load_has_priority_over_up_down: assert property (
        @(posedge clk) disable iff (reset) (load && up_down) |=> (q == $past(q))
    );

    // Full next-state relation when not in reset.
    next_state_functional: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |=> ( q == ( $past(load) ? $past(q)
                                            : ( $past(up_down) ? ($past(q) + 16'd1)
                                                               : ($past(q) - 16'd1) ) ) )
    );
endmodule